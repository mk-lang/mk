use crate::{
    bytes,
    text::{ReadMany, ReadSingle, Source},
    LazyString, ParseResult, Parser,
};

use std::convert::TryInto;
use std::io::Read;
use std::marker::PhantomData;

// Helper function
#[inline(always)]
fn byte_name(b: u8) -> String {
    if b.is_ascii_graphic() {
        ['\'', b as char, '\''].iter().collect()
    } else {
        format!("byte value {:#x}", b)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ByteLiteral<'a>(u8, PhantomData<&'a ()>);

#[inline(always)]
pub fn byte_lit<'a>(b: u8) -> ByteLiteral<'a> {
    ByteLiteral(b, PhantomData)
}

impl<'a, R: Read> Parser<'a, R> for ByteLiteral<'a> {
    type Output = u8;

    #[inline(always)]
    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, u8> {
        match text.read_single() {
            ReadSingle::Error(e) => ParseResult::Error(e),
            ReadSingle::EOF(pos) => {
                if msg_hint {
                    let cloned = *self;
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!("Expected {}, found EOF", byte_name(cloned.0))
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
            ReadSingle::Byte(b, pos) => {
                if self.0 == b {
                    ParseResult::Success(b, pos)
                } else if msg_hint {
                    let cloned = *self;
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!("Expected {}, found {}", byte_name(cloned.0), byte_name(b))
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ByteRange<'a> {
    lower: u8,
    upper: u8,
    _marker: PhantomData<&'a ()>,
}

#[inline(always)]
pub fn byte_range<'a>(lower: u8, upper: u8) -> ByteRange<'a> {
    ByteRange {
        lower,
        upper,
        _marker: PhantomData,
    }
}

impl<'a, R: Read> Parser<'a, R> for ByteRange<'a> {
    type Output = u8;

    #[inline(always)]
    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, u8> {
        match text.read_single() {
            ReadSingle::Error(e) => ParseResult::Error(e),
            ReadSingle::EOF(pos) => {
                if msg_hint {
                    let cloned = *self;
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected a byte at in range {} to {}, found EOF",
                                byte_name(cloned.lower),
                                byte_name(cloned.upper)
                            )
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
            ReadSingle::Byte(b, pos) => {
                if b >= self.lower && b <= self.upper {
                    ParseResult::Success(b, pos)
                } else if msg_hint {
                    let cloned = *self;
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected a byte in range {} to {}, found {}",
                                byte_name(cloned.lower),
                                byte_name(cloned.upper),
                                byte_name(b)
                            )
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteSeq<'a>(Box<[u8]>, PhantomData<&'a ()>);

#[inline(always)]
pub fn byte_seq<'a, S: Into<Box<[u8]>>>(seq: S) -> ByteSeq<'a> {
    ByteSeq(seq.into(), PhantomData)
}

impl<'a, R: Read> Parser<'a, R> for ByteSeq<'a> {
    type Output = Vec<u8>;

    #[inline(always)]
    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, Vec<u8>> {
        match text.read_many(self.0.len()) {
            ReadMany::Error(e) => ParseResult::Error(e),
            ReadMany::EOF(pos) => {
                if msg_hint {
                    let cloned = self.clone();
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected byte sequence {:?}, found EOF",
                                cloned.0.iter().map(|b| format!("{}", b))
                            )
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
            ReadMany::Bytes(seq, pos) => {
                if seq == self.0.as_ref() {
                    ParseResult::Success(seq, pos)
                } else if msg_hint {
                    let cloned = self.clone();
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected byte sequence {:?}, found {:?}",
                                cloned.0.iter().map(|b| format!("{}", b)),
                                seq.iter().map(|b| format!("{}", b))
                            )
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
        }
    }
}

#[derive(Clone,Debug)]
pub struct StringLit<'a> {
    lit: String,
    psr: ByteSeq<'a>,
    _marker: PhantomData<&'a ()>,
}

#[inline(always)]
pub fn string_lit<'a, S: Into<String>>(s: S) -> StringLit<'a> {
    let lit = s.into();
    let psr = byte_seq(Vec::from(lit.clone()));
    StringLit {
        lit,
        psr,
        _marker: PhantomData,
    }
}

impl<'a, R: Read> Parser<'a, R> for StringLit<'a> {
    type Output = &'a str;

    #[inline(always)]
    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, &'a str> {
        match self.psr.parse(text, false) {
            ParseResult::Error(e) => ParseResult::Error(e),
            ParseResult::Success(_,p) => {
                // let lit_ref: &'b str = &self.lit;
                ParseResult::Success(&self.lit, p)
            }
            ParseResult::Fail(p,_,s) => if msg_hint {
                let lit_ref: &'a str = &self.lit;
                ParseResult::Fail(p, 0, Some(LazyString::new(move || {
                    format!("Failed to find string \"{}\":\n{}",
                            &lit_ref, String::from(s.unwrap()))
                })))
            } else {
                ParseResult::Fail(p, 0, None)
            }
        }
    }
}

#[derive(Clone,Debug)]
pub struct CharLit<'a> {
    lit: char,
    psr: ByteSeq<'a>,
    _marker: PhantomData<&'a ()>,
}

// TODO: It would be nice to have no cost for single-byte characters with
// `char_lit` as compared to `byte_lit`
#[inline(always)]
pub fn char_lit<'a>(c: char) -> CharLit<'a> {
    let mut bs = [0u8; 4];

    let psr = byte_seq(Vec::from(c.encode_utf8(&mut bs).as_bytes()));
    CharLit {
        lit: c,
        psr,
        _marker: PhantomData,
    }
}

impl<'a, R: Read> Parser<'a, R> for CharLit<'a> {
    type Output = char;

    #[inline(always)]
    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, char> {
        match self.psr.parse(text, false) {
            ParseResult::Error(e) => ParseResult::Error(e),
            ParseResult::Success(_,p) => ParseResult::Success(self.lit, p),
            ParseResult::Fail(p,_,s) => if msg_hint {
                let lit_cloned: char = self.lit;
                ParseResult::Fail(p, 0, Some(LazyString::new(move || {
                    format!("Failed to find character '{}':\n{}",
                            lit_cloned, String::from(s.unwrap()))
                })))
            } else {
                ParseResult::Fail(p, 0, None)
            },
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CharRange<'a> {
    lower: u32,
    upper: u32,
    _marker: PhantomData<&'a ()>,
}

pub fn char_range<'a>(lower: char, upper: char) -> CharRange<'a> {
    CharRange {
        lower: lower as u32,
        upper: upper as u32,
        _marker: PhantomData,
    }
}

impl<'a, R: Read> Parser<'a, R> for CharRange<'a> {
    type Output = char;

    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, char> {
        // TODO: This function can be optimized much more than it is now.

        // Helper function to avoid code repetition when we fail
        let handle_eof = |pos| {
            if msg_hint {
                let cloned = *self;
                ParseResult::Fail(
                    pos,
                    0,
                    Some(LazyString::new(move || {
                        let lower: char = cloned.lower.try_into().unwrap();
                        let upper: char = cloned.upper.try_into().unwrap();
                        format!("Expected char between {} and {}, found EOF", lower, upper)
                    })),
                )
            } else {
                ParseResult::Fail(pos, 0, None)
            }
        };

        // get the first byte to check the expected length
        let (first, pos) = match text.read_single() {
            ReadSingle::Error(e) => return ParseResult::Error(e),
            ReadSingle::EOF(pos) => return handle_eof(pos),
            ReadSingle::Byte(b, p) => (b, p),
        };

        let req_len = match bytes::expected_utf8_size(first) {
            Err(_) | Ok(None) => {
                return {
                    if msg_hint {
                        ParseResult::Fail(
                            pos,
                            0,
                            Some(LazyString::new(move || {
                                format!(
                                    "{} {:#x} {}",
                                    "Expected unicode character; next byte ",
                                    first,
                                    "is not a valid utf-8 starting byte"
                                )
                            })),
                        )
                    } else {
                        ParseResult::Fail(pos, 0, None)
                    }
                }
            }
            Ok(Some(l)) => l as usize,
        };

        let mut bs = vec![first; req_len];
        match text.read_many(req_len - 1) {
            ReadMany::Error(e) => return ParseResult::Error(e),
            ReadMany::EOF(pos) => return handle_eof(pos),
            ReadMany::Bytes(bytes, _) => bs[1..].copy_from_slice(&bytes),
        }

        // get the unicode value of the bytes
        let u_value = match bytes::decode_utf8(&bs) {
            Err(_) => {
                return if msg_hint {
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected unicode character, got invalid sequence {:?}",
                                bs.iter().map(|b| format!("{:#x}", b))
                            )
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
            // Err(_) => return ParseResult::Fail(None, 0),
            Ok(v) => v,
        };

        if u_value >= self.lower && u_value <= self.upper {
            ParseResult::Success(u_value.try_into().unwrap(), pos)
        } else if msg_hint {
            let cloned = *self;
            ParseResult::Fail(
                pos,
                0,
                Some(LazyString::new(move || {
                    format!(
                        "Parsed unicode value {:?} is outside the range {} to {}",
                        u_value, cloned.lower, cloned.upper
                    )
                })),
            )
        } else {
            ParseResult::Fail(pos, 0, None)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::text::Source;
    use crate::Parser;

    #[test]
    fn lazy_string() {
        let foo = || String::from("foo");
        let lazy = super::LazyString::new(foo);
        assert_eq!(String::from(lazy), "foo");
    }

    #[test]
    fn byte_lit() {
        // TODO: Test position as well
        let s = vec![0x00u8, 0x61, 0x62, 0x63, 0xFF, 0xFE];
        let mut src1 = Source::new(s.as_slice());
        let mut src2 = Source::new(s.as_slice());

        let tab = vec![0x00u8, 0x50, 0x62, 0x63, 0xFF, 0xFF];
        for (&b, &sb) in tab.iter().zip(s.iter()) {
            let psr = super::byte_lit(b);

            let res1 = psr.parse(&mut src1, false);
            let res2 = psr.parse(&mut src2, true);

            if b == sb {
                assert!(res1.is_success());
                assert!(res2.is_success());

                assert_eq!(res1.unwrap().0, b);
                assert_eq!(res2.unwrap().0, b);
            } else {
                assert!(res1.is_fail());
                assert!(res2.is_fail());

                assert!(res1.unwrap_fail().2.is_none());
                assert!(res2.unwrap_fail().2.is_some());
            }
        }
    }

    #[test]
    fn byte_range() {
        // TODO: Test position as well
        let s = vec![0x00, 0x60, 0x70, 0xFF];
        let mut src1 = Source::new(s.as_slice());
        let mut src2 = Source::new(s.as_slice());

        let tab = vec![(0x00, 0x00), (0x10, 0x59), (0x70, 0x80), (0xFF, 0x77)];
        for (&(lower, upper), &b) in tab.iter().zip(s.iter()) {
            let psr = super::byte_range(lower, upper);

            let res1 = psr.parse(&mut src1, false);
            let res2 = psr.parse(&mut src2, true);

            if lower <= b && b <= upper {
                assert!(res1.is_success());
                assert!(res1.is_success());

                assert_eq!(res1.unwrap().0, b);
                assert_eq!(res2.unwrap().0, b);
            } else {
                assert!(res1.is_fail());
                assert!(res2.is_fail());

                assert!(res1.unwrap_fail().2.is_none());
                assert!(res2.unwrap_fail().2.is_some());
            }
        }
    }

    #[test]
    fn byte_seq() {
        let s = vec![0x00u8, 0x61, 0x62, 0x63, 0xFF, 0xFE, 0x01, 0x02, 0x03, 0x04];
        let mut src1 = Source::new(s.as_slice());
        let mut src2 = Source::new(s.as_slice());

        // let tab: Vec<(Vec<u8>, bool)> = vec![
        let tab = vec![
            (vec![0x00, 0x61], true),
            (vec![0x62, 0x64], false),
            (vec![0x00, 0xFE], false),
            (vec![0x01, 0x02, 0x03, 0x04], true),
        ];
        for (seq, m) in tab.into_iter() {
            let psr = super::byte_seq(seq.clone());
            let res1 = psr.parse(&mut src1, false);
            let res2 = psr.parse(&mut src2, true);

            // m gives whether we expect a match or not
            if m {
                assert!(res1.is_success());
                assert!(res1.is_success());

                assert_eq!(res1.unwrap().0, seq);
                assert_eq!(res2.unwrap().0, seq);
            } else {
                assert!(res1.is_fail());
                assert!(res2.is_fail());

                assert!(res1.unwrap_fail().2.is_none());
                assert!(res2.unwrap_fail().2.is_some());
            }
        }
    }

    #[test]
    fn string_lit() {
        let s = String::from("foo bar string");
        let mut src = Source::new(s.as_bytes());
        assert!(super::string_lit("foo").parse(&mut src, false).is_success());
        assert!(super::string_lit("abcde").parse(&mut src, false).is_fail());
        assert!(super::string_lit("string")
            .parse(&mut src, false)
            .is_success());
    }

    #[test]
    fn char_lit() {
        let s = String::from("ab☺é");
        let mut src = Source::new(s.as_bytes());
        assert!(super::char_lit('a').parse(&mut src, false).is_success());
        assert!(super::char_lit('c').parse(&mut src, false).is_fail());
        assert!(super::char_lit('☺').parse(&mut src, false).is_success());
        assert!(super::char_lit('é').parse(&mut src, false).is_success());
    }

    #[test]
    fn char_range() {
        let s = String::from("☺");
        let mut src = Source::new(s.as_bytes());
        assert!(super::char_range('a', '♋')
            .parse(&mut src, false)
            .is_success());
    }
}