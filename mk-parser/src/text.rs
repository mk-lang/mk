use std::io::Read;

use crate::bytes;
use crate::Pos;

// TODO: Add another enum - `ReadMany` - which gives Vec<u8>
#[derive(Debug)]
#[must_use] // TODO: Add message detailing why it should be used
pub enum ReadSingle {
    Byte(u8, Pos),
    EOF(Pos),
    Error(std::io::Error),
}

// TODO: Document
#[derive(Debug)]
#[must_use] // TODO: Add message detailing why it should be used
pub enum ReadMany {
    Bytes(Vec<u8>, Pos),
    EOF(Pos),
    Error(std::io::Error),
}

impl ReadSingle {
    pub fn is_byte(&self) -> bool {
        match self {
            ReadSingle::Byte(_, _) => true,
            _ => false,
        }
    }

    pub fn is_eof(&self) -> bool {
        match self {
            ReadSingle::EOF(_) => true,
            _ => false,
        }
    }

    pub fn is_err(&self) -> bool {
        match self {
            ReadSingle::Error(_) => true,
            _ => false,
        }
    }

    pub fn unwrap(self) -> (u8, Pos) {
        match self {
            ReadSingle::Byte(b, p) => (b, p),
            ReadSingle::EOF(_) => panic!("Called `ReadSingle::unwrap()` on an `EOF` value"),
            ReadSingle::Error(_) => panic!("Called `ReadSingle::unwrap()` on an `Error` value"),
        }
    }
}

impl ReadMany {
    pub fn is_bytes(&self) -> bool {
        match self {
            ReadMany::Bytes(_, _) => true,
            _ => false,
        }
    }

    pub fn is_eof(&self) -> bool {
        match self {
            ReadMany::EOF(_) => true,
            _ => false,
        }
    }

    pub fn is_err(&self) -> bool {
        match self {
            ReadMany::Error(_) => true,
            _ => false,
        }
    }

    pub fn unwrap(self) -> (Vec<u8>, Pos) {
        match self {
            ReadMany::Bytes(b, p) => (b, p),
            ReadMany::EOF(_) => panic!("Called `ReadMany::unwrap()` on an `EOF` value"),
            ReadMany::Error(_) => panic!("Called `ReadMany::unwrap()` on an `Error` value"),
        }
    }
}

// We make the buffer have a size of 4096 so that we can efficiently read
// each file sector
const SOURCE_BUF_SIZE: usize = 4096;

// TODO: Document
// Need to make a note about how it's **only** utf-8
// Note that it assumes EOF if the reader gives 0 bytes
pub struct Source<R: Read> {
    reader: R,
    empty: bool,

    // main buffer info
    //
    // `buf` and `poss` are stored in different ways. For `buf`, the last byte
    // of the previous buffer is stored in index 0, so we always get from index
    // i+1, whereas poss stores the position for index `i` AT index i
    //
    // Note that `buf_end` will always be the **number** of bytes read into the
    // buffer - not the upper (exclusie) bound on the last index.
    buf: [u8; SOURCE_BUF_SIZE + 1],
    poss: [Pos; SOURCE_BUF_SIZE + 1],
    buf_end: usize,

    // switch between main buffer and backtrack buffer, with indexes for both
    idx: ReadIdx,

    bkstat: BacktrackStat,
}

#[derive(Debug)]
struct BacktrackStat {
    marks: Vec<usize>,
    // `stored` and `poss` are always guaranteed to have the same length
    stored: Vec<u8>,
    poss: Vec<Pos>,
    // TODO: Describe this. It's usually zero, which is why it's safe to add.
    buf_offset: usize,
}

#[derive(Debug)]
enum ReadIdx {
    // Indicates that we're currently drawing from the stored backtracking
    // buffer, giving the index in that buffer of the next value. The given
    // index will always be less than the length of that buffer.
    //
    // Once the index reaches the end of the backtrack buffer, the value of
    // this enum will be incremented to `MainBuf(0)`.
    Backtracked(usize),

    // Indicates that we're currently getting bytes from the "normal" buffer,
    // giving the index that we're about to get bytes from.
    //
    // Note: This value **can** equal SOURCE_BUF_SIZE, in which case the buffer
    // must be refilled before any more bytes can be read.
    //
    // Note again: The index we're about to get bytes from is actually
    // (index + 1), because index 0 is reserved for the last byte of the
    // previous buffer.
    MainBuf(usize),
}

impl<R: Read> Source<R> {
    /// Creates a new `Source` from a `File`
    pub fn new(reader: R) -> Source<R> {
        Source {
            reader,
            empty: false,
            buf: [0u8; SOURCE_BUF_SIZE + 1],
            poss: [Pos { line: 1, col: 1 }; SOURCE_BUF_SIZE + 1],
            buf_end: 0,
            idx: ReadIdx::MainBuf(0),
            bkstat: BacktrackStat {
                marks: Vec::new(),
                stored: Vec::new(),
                poss: Vec::new(),
                buf_offset: 0,
            },
        }
    }

    /// Returns the position of the next character to be read, starting at
    /// line 1, column 1.
    ///
    /// If we have already reached the end of the reader, this will give the
    /// position of the last character, with the column number incremented once
    /// (as if there were another character beyond it).
    ///
    /// This will treat each byte as a new 'character' so as to avoid needing
    /// to do any utf-8 decoding here - the line number will increment every
    /// time any one of the following characters are encountered:
    /// * 0x0A (line feed, '\n')
    /// * 0x0B (vertical tab, '\v')
    /// * 0x0C (form feed)
    /// * 0x0D (carriage return, '\r')
    /// * U+0085 (next line)
    /// Note that 'U+0085' requires two bytes, so we do some additional storage
    /// in case we come across the two in sequence.
    // TODO: Is the above list complete?
    // TODO: Should we actually allow carriage returns?
    #[inline(always)]
    pub fn pos(&self) -> Pos {
        match self.idx {
            ReadIdx::Backtracked(i) => self.bkstat.poss[i],
            ReadIdx::MainBuf(i) => self.poss[i],
        }
    }

    // Reads the reader into the buffer, storing them into the backtracking list
    // if necessary.
    //
    // Note that this does not change the current index - that must be done by
    // the caller.
    fn fill_buf(&mut self) -> Option<std::io::Error> {
        // Handle backtracking... If we're storing for possible future
        // backtracking, we'll want to store the current contents and
        // positions of the buffer
        if self.bkstat.marks.is_empty() {
            let o = self.bkstat.buf_offset;
            let e = self.buf_end;

            #[allow(clippy::range_plus_one)]
            self.bkstat
                .stored
                .extend_from_slice(&self.buf[o + 1..e + 1]);
            self.bkstat.poss.extend_from_slice(&self.poss[o..e]);
            self.bkstat.buf_offset = 0;
        }

        self.buf[0] = self.buf[self.buf_end];
        self.poss[0] = self.poss[self.buf_end];

        // Now we try to refill the buffer. We start from index 1, not 0
        // because `buf` stores the last byte of the previous buffer in index
        // 0. For more info, see the comment describing `buf`.
        match self.reader.read(&mut self.buf[1..]) {
            Err(e) => Some(e),
            Ok(n) => {
                self.buf_end = n;

                if n == 0 {
                    self.empty = true;
                }

                None
            }
        }
    }

    // Gets the next byte to read, along with its position, WITHOUT filling the
    // buffer. This is unsafe because improper usage has the possibility of
    // silently going wrong.
    //
    // After getting the next byte, this function increments `idx`.
    #[inline(always)]
    unsafe fn get_byte_and_pos(&mut self) -> (u8, Pos) {
        match self.idx {
            ReadIdx::MainBuf(i) => {
                self.idx = ReadIdx::MainBuf(i + 1);

                // The bytes corresponding to the utf-8 encoding of U+0085
                // ("next line") are what is given below.
                let Pos { line: ln, col: c } = self.poss[i];

                // Check for new lines:
                if bytes::is_new_line(self.buf[i + 1]) {
                    self.poss[i + 1] = Pos {
                        line: ln + 1,
                        col: 1,
                    };
                } else {
                    self.poss[i + 1] = match self.buf[i..=i + 1] {
                        [0xC2, 0x85] => Pos {
                            line: ln + 1,
                            col: 1,
                        },
                        _ => Pos {
                            line: ln,
                            col: c + 1,
                        },
                    };
                }

                (self.buf[i + 1], self.poss[i])
            }
            ReadIdx::Backtracked(i) => {
                if i + 1 == self.bkstat.stored.len() {
                    self.idx = ReadIdx::MainBuf(0);

                    // If we're no longer using the backtracked values, we'll
                    // clear them.
                    if self.bkstat.marks.is_empty() {
                        self.bkstat.stored = Vec::new();
                        self.bkstat.poss = Vec::new();
                        self.bkstat.buf_offset = 0;
                    }
                } else {
                    self.idx = ReadIdx::Backtracked(i + 1);
                }

                (self.bkstat.stored[i], self.bkstat.poss[i])
            }
        }
    }

    /// Reads a single byte from the reader. If the `Source` has backtracked,
    /// the byte may be from a stored backtracking buffer instead.
    pub fn read_single(&mut self) -> ReadSingle {
        if self.empty {
            return ReadSingle::EOF(self.pos());
        }

        let i = match self.idx {
            ReadIdx::MainBuf(i) => i,
            ReadIdx::Backtracked(_) => {
                let (byte, pos) = unsafe { self.get_byte_and_pos() };
                return ReadSingle::Byte(byte, pos);
            }
        };

        // we'll need to refill the buffer if we're at the last index
        if i == self.buf_end {
            if let Some(e) = self.fill_buf() {
                return ReadSingle::Error(e);
            } else if self.empty {
                return ReadSingle::EOF(self.pos());
            }

            self.idx = ReadIdx::MainBuf(0);
        }

        let (byte, pos) = unsafe { self.get_byte_and_pos() };
        ReadSingle::Byte(byte, pos)
    }

    /// Reads `n` bytes from the reader. If it encounters EOF before the end,
    /// no bytes will be returned (it will be EOF instead), but the `Source`
    /// will have been modified to have already "read" those bytes - retrieving
    /// them will need to be done through backtracking.
    ///
    /// The returned position is given by the *start* of the range - both for
    /// `ReadMany::Bytes` **and** `ReadMany::EOF`
    pub fn read_many(&mut self, n: usize) -> ReadMany {
        let mut return_buf = Vec::with_capacity(n);
        let pos = self.pos();

        while return_buf.len() != n {
            if self.empty {
                return ReadMany::EOF(pos);
            }

            match self.idx {
                ReadIdx::MainBuf(mut i) => {
                    if i == self.buf_end {
                        if let Some(err) = self.fill_buf() {
                            return ReadMany::Error(err);
                        }

                        i = 0;
                    }

                    let end_i = if n <= self.buf_end - i {
                        i + n
                    } else {
                        self.buf_end
                    };

                    self.idx = ReadIdx::MainBuf(end_i);

                    // update positions across the range
                    for idx in i..end_i {
                        let Pos { line: ln, col: c } = self.poss[idx];

                        let newline = bytes::is_new_line(self.buf[idx + 1])
                            || self.buf[i..=i + 1] == [0xC2, 0x85];

                        self.poss[idx + 1] = if newline {
                            Pos {
                                line: ln + 1,
                                col: 1,
                            }
                        } else {
                            Pos {
                                line: ln,
                                col: c + 1,
                            }
                        };
                    }

                    // copy the bytes
                    #[allow(clippy::range_plus_one)]
                    return_buf.extend_from_slice(&self.buf[i + 1..end_i + 1]);
                }
                ReadIdx::Backtracked(i) => {
                    let end_i = if n < self.bkstat.stored.len() - i {
                        self.idx = ReadIdx::Backtracked(i + n);
                        i + n
                    } else {
                        self.idx = ReadIdx::MainBuf(0);
                        self.bkstat.stored.len()
                    };

                    return_buf.extend_from_slice(&self.bkstat.stored[i..end_i]);
                }
            }
        }

        ReadMany::Bytes(return_buf, pos)
    }

    // TODO: Document
    pub fn mark_backtrack(&mut self) {
        // If the length is zero, we'd be adding the first backtracking mark.
        if self.bkstat.marks.is_empty() {
            match self.idx {
                ReadIdx::MainBuf(i) => self.bkstat.buf_offset = i,
                ReadIdx::Backtracked(i) => {
                    // TODO: Assess the following:
                    // Currently, it's possible to continue to add to the
                    // backtracking buffer indefinitely, even without always
                    // having a mark active. This is because we only clear the
                    // buffer once we leave AND there are no marks left, so if
                    // new marks are added before we have time to clear the
                    // buffer, this may be an issue.
                    //
                    // For the meantime, we'll just do it as-is
                    self.bkstat.marks = vec![i];
                    return;
                }
            }
        }

        match self.idx {
            ReadIdx::MainBuf(i) => {
                let idx = i + self.bkstat.stored.len() - self.bkstat.buf_offset;
                self.bkstat.marks.push(idx);
            }
            ReadIdx::Backtracked(i) => self.bkstat.marks.push(i),
        }
    }

    // TODO: Document
    pub fn unmark_backtrack(&mut self) {
        // We'll just assert that there **was** a mark to get rid of in the
        // first place
        if self.bkstat.marks.pop().is_none() {
            panic!(
                "Tried to `unmark_backtrack`, {}",
                "but there are no marks to remove"
            );
        }

        // If there aren't any more backtrack marks and we're not using the
        // buffer, we can get rid of it. Otherwise, it'll get removed later.
        if let ReadIdx::MainBuf(_) = self.idx {
            if self.bkstat.marks.is_empty() {
                self.bkstat.stored = Vec::new();
                self.bkstat.poss = Vec::new();
                self.bkstat.buf_offset = 0;
            }
        }
    }

    // TODO: Document
    pub fn backtrack(&mut self) {
        if self.bkstat.marks.is_empty() {
            panic!("Can't backtrack; no marks set");
        }

        let bk_idx = self.bkstat.marks[self.bkstat.marks.len() - 1];
        self.idx = match self.idx {
            ReadIdx::Backtracked(_) => ReadIdx::Backtracked(bk_idx),
            ReadIdx::MainBuf(_) => {
                let len = self.bkstat.stored.len();
                if bk_idx >= len {
                    ReadIdx::MainBuf(bk_idx - len + self.bkstat.buf_offset)
                } else {
                    ReadIdx::Backtracked(bk_idx)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn text_source_single_no_backtrack() {
        // Note that this test does not cause us to need to refill the buffer
        // more than once.
        //
        // Unofficially, that can be remedied by setting the constant to a very
        // low value and running the tests twice.

        let s = "foo\na\x0Bb\u{0085}c";

        // The right-hand column gives the positions as a tuple
        let expecting = [
            (0x66u8, (1, 1)), // f
            (0x6F, (1, 2)),   // o
            (0x6F, (1, 3)),   // o
            (0x0A, (1, 4)),   // \n
            (0x61, (2, 1)),   // a
            (0x0B, (2, 2)),   // vertical tab
            (0x62, (3, 1)),   // b
            (0xC2, (3, 2)),   // first byte of unicode "next line"
            (0x85, (3, 3)),   // second byte
            (0x63, (4, 1)),   // c
        ];

        let mut src = Source::new(s.as_bytes());
        for &(expected_byte, (line, col)) in expecting.iter() {
            let res = src.read_single();
            assert!(!res.is_eof());
            assert!(!res.is_err());
            let (byte, pos) = res.unwrap();

            let expected_pos = Pos { line, col };
            assert_eq!(pos, expected_pos);
            assert_eq!(byte, expected_byte);
        }
        assert!(src.read_single().is_eof());
    }

    #[test]
    fn text_source_single_backtrack() {
        // Note that this test does not cause us to need to refill the buffer
        // more than once.
        //
        // Unofficially, that can be remedied by setting the constant to a very
        // low value and running the tests twice.
        // * For this test, the buffer size would need to be **very** low:
        //   probably 1 or 2.

        let s = "a\nb\u{0085}c";

        // We're running this so that we go in order:
        // * possibly mark,
        // * possibly backtrack
        // * possibly unmark
        // * get byte/pos
        // The ordering of the tuple reflects this. The final elements are the
        // expected byte and position
        let all: [(bool, bool, bool, u8, (u32, u32)); 14] = [
            (true, true, true, 0x61, (1, 1)),    // a
            (true, false, false, 0x0A, (1, 2)),  // \n
            (false, false, false, 0x62, (2, 1)), // b
            //
            (false, true, false, 0x0A, (1, 2)),  // back to '\n'
            (false, false, false, 0x62, (2, 1)), // b
            //
            (false, true, false, 0x0A, (1, 2)),  // back to '\n'
            (false, false, false, 0x62, (2, 1)), // b
            (false, false, false, 0xC2, (2, 2)), // first byte of unicode "next line"
            (true, false, false, 0x85, (2, 3)),  // second byte
            (false, false, false, 0x63, (3, 1)), // c
            //
            (false, true, true, 0x85, (2, 3)), // back to second byte of "next line"
            (false, false, false, 0x63, (3, 1)), // c
            //
            (false, true, true, 0x0A, (1, 2)),   // back to '\n'
            (false, false, false, 0x62, (2, 1)), // b
        ];

        let mut src = Source::new(s.as_bytes());
        for &(m, bk, u, b, (l, c)) in all.iter() {
            if m {
                src.mark_backtrack();
            }
            if bk {
                src.backtrack();
            }
            if u {
                src.unmark_backtrack();
            }

            let pos = Pos { line: l, col: c };

            let res = src.read_single();
            assert!(!res.is_eof());
            if res.is_err() {
                panic!("{:?}", res);
            }

            let (get_b, get_pos) = res.unwrap();

            assert_eq!(pos, get_pos);
            assert_eq!(b, get_b);
        }
    }

    #[test]
    fn text_source_many_no_backtrack() {
        // Note that this test does not cause us to need to refill the buffer
        // more than once.
        //
        // Unofficially, that can be remedied by setting the constant to a very
        // low value and running the tests twice.

        let s = "foo\na\x0Bb\u{0085}c";

        // The right-hand column gives the positions as a tuple
        let expecting = [
            (vec![0x66u8, 0x6F], (1, 1)),
            (vec![0x6F, 0x0A, 0x61], (1, 3)),
            (vec![0x0B, 0x62, 0xC2], (2, 2)),
            (vec![0x85, 0x63], (3, 3)),
        ];

        let mut src = Source::new(s.as_bytes());
        for (i, (e_bytes, (line, col))) in expecting.iter().enumerate() {
            println!("{:?}", i);

            let res = src.read_many(e_bytes.len());
            assert!(!res.is_eof());
            assert!(!res.is_err());
            let (bytes, pos) = res.unwrap();

            let e_pos = Pos {
                line: *line,
                col: *col,
            };
            assert_eq!(pos, e_pos);
            assert_eq!(&bytes, e_bytes);
        }
        assert!(!src.read_many(0).is_eof());
        assert!(src.read_many(1).is_eof());
    }
}
