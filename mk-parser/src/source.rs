//! Definition of `Source` and associated types
//!
//! The [`Source`] type is used to provide a buffered stream of bytes to
//! [`Parser`]s - the primary purpose of this crate.
//!
//! The two other types given in this module - `ReadSingle` and `ReadMany` -
//! are the result types for reading from a `Source`; `ReadSingle` wraps a
//! single `u8` and `ReadMany` a `Vec<u8>`. Unless you are defining your own
//! `Parser` type, however, these details will be largely irrelevant.
//!
//! [`Source`]: struct.Source.html
//! [`Parser`]: ../trait.Parser.html

use std::io::Read;

use crate::bytes;
use crate::Pos;

/// Represents the outcome of reading a single byte from a `Source`
///
/// This type is only used in the context of [`Source::read_single`],
/// so it should be interpreted as such.
///
/// All provided methods are simply the deconstructors for the type
///
/// [`Source::read_single`]: struct.Source.html#method.read_single
#[derive(Debug)]
#[must_use = "This could be an `Error` variant, which should be handled"]
pub enum ReadSingle {
    /// A successful read, yielding a single byte and its position
    Byte(u8, Pos),

    /// Indicates that there were no more bytes to read, giving the current
    /// position of the `Source`
    EOF(Pos),

    /// Represents an error that occured while reading
    Error(std::io::Error),
}

/// Represents the outcome of reading some number of bytes from a `Source`
///
/// This type is only used in the context of the methods on [`Source`], so
/// it should be interpreted as such.
///
/// Note that it is perfectly valid for the vector in `Bytes` to be empty -
/// whether or not this is possible depends on the function this results from.
///
/// All provided methods are simply the deconstructors for the type.
///
/// [`Source`]: struct.Source.html
#[derive(Debug)]
#[must_use = "This could be an `Error` variant, which should be handled"]
pub enum ReadMany {
    /// A successful read, yielding a set of bytes and the starting position
    Bytes(Vec<u8>, Pos),

    /// Indicates that there was not a sufficient number of bytes left
    /// available to read, giving the position of the start of the would-be
    /// sequence.
    EOF(Pos),
    
    /// Represents an error that occured while reading
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

    pub fn unwrap_err(self) -> std::io::Error {
        match self {
            ReadSingle::Byte(_,_) => panic!("Called `ReadSingle::unwrap_err()` on a `Byte` value"),
            ReadSingle::EOF(_) => panic!("Called `ReadSingle::unwrap_err()` on an `EOF` value"),
            ReadSingle::Error(e) => e,
        }
    }

    pub fn pos(&self) -> Pos {
        match self {
            ReadSingle::Byte(_, p) => *p,
            ReadSingle::EOF(p) => *p,
            ReadSingle::Error(_) => panic!("Called `ReadSingle::pos()` on an `Error` value, which has none"),
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

    pub fn unwrap_err(self) -> std::io::Error {
        match self {
            ReadMany::Bytes(_,_) => panic!("Called `ReadMany::unwrap_err()` on a `Bytes` value"),
            ReadMany::EOF(_) => panic!("Called `ReadMany::unwrap_err()` on an `EOF` value"),
            ReadMany::Error(e) => e,
        }
    }

    pub fn pos(&self) -> Pos {
        match self {
            ReadMany::Bytes(_, p) => *p,
            ReadMany::EOF(p) => *p,
            ReadMany::Error(_) => panic!("Called `ReadMany::pos()` on an `Error` value, which has none"),
        }
    }
}

// This is the size that the standard library uses internally for reading from
// files, so it should have no overhead aside from copy the bits
const SOURCE_BUF_SIZE: usize = 4096;

/// A buffered, backtracking byte-stream to provide to [`Parser`]s
///
/// # Usage
///
/// This will typically be created from a file for use directly with a parser:
/// ```no_run
/// # use mk_parser::{
/// #     source::Source,
/// #     Parser,
/// #     DynParser,
/// # };
/// use std::io::Read;
/// use std::fs::File;
///
/// # fn main() -> std::io::Result<()> {
/// let mut file = File::open("foo.txt")?;
/// let src = Source::new(file);
///
/// let parser = { /* ... */ };
/// # let parser: Box<dyn DynParser<Output=()>> = unimplemented!();
///
/// let result = parser.parse(&mut src, false);
/// # Ok(())
/// # }
/// ```
///
/// The `Source` type also supports backtracking. This is described in the
/// documentation for [`Source::backtrack()`]
///
/// Please note: In order for the positions given to work correctly, the input
/// data should be UTF-8 encoded (or ASCII, as it is forwards compatible with
/// UTF-8).
///
/// Additionally: One of the base asumptions made about the provided byte-stream
/// is that it will give zero bytes once it has been exhausted, so `Source` will
/// give `EOF` once that has happened. This should not be an issue unless you
/// are implementing your own [`Read`] type.
///
/// [`Parser`]: ../trait.DynParser.html
/// [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
/// [`Source::backtrack()`]: #method.backtrack
pub struct Source<'a> {
    reader: Box<dyn 'a + Read>,
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

impl<'a> Source<'a> {
    /// Creates a new `Source` from an [`io::Read`]
    ///
    /// The `Read` type here will typically be a file:
    /// ```no_run
    /// # use mk_parser::source::Source;
    /// use std::io::Read;
    /// use std::fs::File;
    ///
    /// # fn main() -> std::io::Result<()> {
    /// let mut file = File::open("foo.txt")?;
    /// let src = Source::new(file);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new<R: 'a + Read>(reader: R) -> Source<'a> {
        Source {
            reader: Box::new(reader),
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
    /// Columns are calculated by bytes, not characters, to avoid doing any
    /// UTF-8 decoding. Line numbers incremeent every time any one of the
    /// following characters are encountered:
    /// * 0x0A (line feed, '\n')
    /// * 0x0B (vertical tab, '\v')
    /// * 0x0C (form feed)
    /// * 0x0D (carriage return, '\r')
    /// * U+0085 (next line)
    /// Note that 'U+0085' requires two bytes, so we do some additional storage
    /// in case we come across the two in sequence.
    // TODO: Is the above list complete?
    // TODO: Should we actually allow carriage returns?
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
        if !self.bkstat.marks.is_empty() {
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

    /// Reads a single byte
    ///
    /// If there are no more bytes to read, this will return
    /// [`ReadSingle::EOF`].
    ///
    /// Note that if it has backtracked, the byte may be from an intern buffer,
    /// not directly from the input byte-stream
    ///
    /// [`ReadSingle::EOF`]: enum.ReadSingle.html#variant.EOF
    pub fn read_single(&mut self) -> ReadSingle {
        // TODO: Benchmark a dedicated function
        match self.read_many(1) {
            ReadMany::Error(e) => ReadSingle::Error(e),
            ReadMany::EOF(p) => ReadSingle::EOF(p),

            // We can take the 0th index because we know that there's always
            // going to be exactly 1 byte
            ReadMany::Bytes(bs, p) => ReadSingle::Byte(bs[0], p),
        }
    }

    /// Reads `n` bytes
    ///
    /// If there aren't enough bytes left, [`ReadMany::EOF`] will be returned
    /// instead, but those bytes will still have been "consumed" - retrieving
    /// them must be done through backtracking.
    ///
    /// Whether this returns `ReadMany::Bytes` or `ReadMany::EOF`, the position
    /// will be given by the start of the range.
    ///
    /// [`ReadMany::EOF`]: enum.ReadMany.html#variant.EOF
    pub fn read_many(&mut self, n: usize) -> ReadMany {
        // TODO: Benchmark a dedicated function
        if n == 0 {
            return ReadMany::Bytes(Vec::new(), self.pos());
        }

        let mut so_far = 0;
        self.read_until(|_, _| {
            so_far += 1;
            so_far == n
        })
    }

    // Yields bytes **while** pred is true.
    // TODO: Write a describing comment for this function
    fn read_pred_internal<P: FnMut(u8, Pos) -> bool>(
        &mut self,
        mut pred: P,
        size_hint: usize,
        fail_eof: bool,
        rm_last: bool,
    ) -> ReadMany {
        let mut return_buf = Vec::with_capacity(size_hint);

        let start_pos = self.pos();

        loop {
            if self.empty {
                return match fail_eof {
                    false => ReadMany::Bytes(return_buf, start_pos),
                    true => ReadMany::EOF(start_pos),
                };
            }

            // Get more bytes to read
            match self.idx {
                ReadIdx::Backtracked(i) => {
                    // If it's backtracked, we just want to get as much of it
                    // as possible
                    let mut end = i;

                    let done = loop {
                        let b = self.bkstat.stored[end];
                        let p = self.bkstat.poss[end];

                        end += 1;

                        if !pred(b, p) {
                            break true;
                        } else if end == self.bkstat.stored.len() {
                            break false;
                        }
                    };

                    // Add what we've read to the return buffer
                    return_buf.extend_from_slice(&self.bkstat.stored[i..end]);

                    if done && rm_last {
                        end -= 1;
                    }

                    if end == self.bkstat.stored.len() {
                        self.idx = ReadIdx::MainBuf(0)
                    } else {
                        self.idx = ReadIdx::Backtracked(end)
                    };

                    if done {
                        return ReadMany::Bytes(return_buf, start_pos);
                    }
                }
                ReadIdx::MainBuf(mut i) => {
                    // Refill the buffer if we need to
                    if i == self.buf_end {
                        if let Some(err) = self.fill_buf() {
                            return ReadMany::Error(err);
                        }

                        // The handling for being empty is at the top of the
                        // loop, so we'll just do it there.
                        if self.empty {
                            continue;
                        }

                        i = 0;
                    }

                    let mut end = i;

                    let done = loop {
                        let b = self.buf[end + 1];
                        let p = self.poss[end];

                        // We need to calculate the next position, so we'll
                        // first see this byte represents a newline.
                        //
                        // Note that [0xC2, 0x85] makes the bytes of the utf-8
                        // encoding for the unicode "next line" character
                        let is_newline =
                            bytes::is_new_line(b) || self.buf[end..=end + 1] == [0xC2, 0x85];

                        self.poss[end + 1] = match is_newline {
                            true => Pos {
                                line: p.line + 1,
                                col: 1,
                            },
                            false => Pos {
                                col: p.col + 1,
                                ..p
                            },
                        };

                        end += 1;

                        if !pred(b, p) {
                            break true;
                        } else if end == self.buf_end {
                            break false;
                        }
                    };

                    if done && rm_last {
                        end -= 1;
                    }

                    self.idx = ReadIdx::MainBuf(end);

                    // We add one on both because `buf` is offset one
                    #[allow(clippy::range_plus_one)]
                    return_buf.extend_from_slice(&self.buf[i + 1..end + 1]);

                    if done {
                        return ReadMany::Bytes(return_buf, start_pos);
                    }
                }
            }
        }
    }

    /// Reads bytes **until** the predicate is true
    ///
    /// A successful read will be terminated by a byte for which the predicate
    /// evaluates to true - this is included in the output. If the predicate
    /// never evaluates to true, [`ReadMany::EOF`] will be returned.
    ///
    /// Please note that this function is different from [`read_while`] in a
    /// couple ways, aside from the predicate simply being inverted. Please see
    /// its documentation for more information.
    ///
    /// [`ReadMany::EOF`]: enum.ReadMany.html#variant.EOF
    /// [`read_while`]: #method.read_while
    pub fn read_until<P: FnMut(u8, Pos) -> bool>(&mut self, mut predicate: P) -> ReadMany {
        self.read_pred_internal(|b, p| !predicate(b, p), 1, true, false)
    }

    /// Reads bytes **while** the predicate is true
    ///
    /// A successful read consists of any number of sequential bytes for which
    /// the predicate evaluated to true. Note that this number can be zero, and
    /// that reaching EOF is equivalent to the predicate evaluating to false -
    /// we will return early.
    ///
    /// This implies that this method can never return [`ReadMany::EOF`].
    ///
    /// For different behavior, please see [`read_until`].
    ///
    /// [`ReadMany::EOF`]: enum.ReadMany.html#variant.EOF
    /// [`read_until`]: #method.read_until
    pub fn read_while<P: FnMut(u8, Pos) -> bool>(&mut self, mut predicate: P) -> ReadMany {
        self.read_pred_internal(|b, p| predicate(b, p), 0, false, true)
    }

    /// Marks the current position to be backtracked to
    ///
    /// For information on backtracking, see [`Source::backtrack`]
    ///
    /// [`Source::backtrack`]: #method.backtrack
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

    /// Unmarks the most recent backtracking mark
    ///
    /// For information on backtracking, see [`Source::backtrack`]
    ///
    /// [`Source::backtrack`]: #method.backtrack
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

    /// Backtracks to the most recent mark
    ///
    /// # Backtracking
    ///
    /// Sometimes it is useful to understand the internals of a function to
    /// understand its behavior. This is one of those cases.
    ///
    /// Backtracking is represented internally with an optional buffer and a
    /// list of positions we might backtrack to. If the list isn't empty (i.e.
    /// if we could need to backtrack), more data is added to the buffer only
    /// when we refill the main file buffer.
    ///
    /// Adding a mark for backtracking is just pushing the position to the end
    /// of the list, and unmarking is popping the last.
    ///
    /// Backtracking within the main file buffer incurs no additional cost -
    /// neither does nested backtracking (having many marks).
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

    #[test]
    fn source_single_no_backtrack() {
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
    fn source_single_backtrack() {
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
    fn source_many_no_backtrack() {
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
            println!("{}", i);

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

    #[test]
    fn source_read_until() {
        let s = "foo\na\x0Bb\u{0085}c";
        let mut src = Source::new(s.as_bytes());

        let res = src.read_until(|b, _| b as char == 'a');
        assert!(!res.is_eof());
        assert!(!res.is_err());
        assert_eq!(res.unwrap().0, "foo\na".as_bytes());

        let res = src.read_until(|b, _| b as char == 'b');
        assert!(!res.is_eof());
        assert!(!res.is_err());
        let (s, p) = res.unwrap();
        assert_eq!(p, Pos::from((2, 2)));
        assert_eq!(s, "\x0Bb".as_bytes());

        assert_eq!(src.pos(), Pos::from((3, 2)));

        let res = src.read_until(|b, _| b as char == 'd');
        assert!(res.is_eof());
    }

    #[test]
    fn source_read_while() {
        let s = "foo\na\x0Bb\u{0085}c";
        let mut src = Source::new(s.as_bytes());

        let res = src.read_while(|b, _| b as char != 'a');
        assert!(!res.is_eof());
        assert!(!res.is_err());
        assert_eq!(res.unwrap().0, "foo\n".as_bytes());

        let res = src.read_while(|b, _| b as char != 'b');
        assert!(!res.is_eof());
        assert!(!res.is_err());
        assert_eq!(res.unwrap().0, "a\x0B".as_bytes());

        let res = src.read_while(|b, _| b as char != 'd');
        assert!(!res.is_eof());
        assert!(!res.is_err());
        assert_eq!(res.unwrap().0, "b\u{0085}c".as_bytes());
    }
}
