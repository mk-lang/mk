//! Simple, commonly-used parsers
//!
//! Provided here are many of the [`Parser`]s that are the building blocks of a
//! more complicated system. Most of them have an associated constructor
//! function.
//!
//! For parsers that are more fundamental to the input stream of bytes, see
//! [`fundamentals`].
//!
//! [`Parser`]: ../trait.Parser.html
//! [`fundamentals`]: ../fundamentals/index.html

use crate::{
    bytes,
    fundamentals::{ByteSeq, ByteLit},
    source::{ReadMany, ReadSingle, Source},
    utils::LazyString,
    DynParser, ParseResult, Parser,
};

use std::{
    convert::{TryInto, TryFrom},
    ops::{BitOr, Add}
};

/// Parser that matches on a literal string
///
/// This type requires an owned `String`. For matching with just a
/// reference, see [`StrLit`].
///
/// This parser internally uses [`fundamentals::ByteSeq`], so all of its
/// behavior (e.g. always consuming bytes equal to the length of the string)
/// comes from there.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::basics::StringLit;
///
/// let s = String::from("foo-bar");
/// let mut src = Source::new(s.as_bytes());
///
/// let foo = StringLit(String::from("foo"));
/// let bar = StringLit(String::from("-bar"));
///
/// assert!(foo.parse(&mut src, false).is_success());
/// assert!(bar.parse(&mut src, false).is_success());
/// ```
///
/// [`StrLit`]: struct.StrLit.html
/// [`fundamentals::ByteSeq`]: ../fundamentals/struct.ByteSeq.html
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct StringLit(pub String);

impl DynParser for StringLit {
    type Output = String;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<String> {
        let ptr = &self.0 as *const String as *const ByteSeq<String>;
        let psr = unsafe { &*ptr };

        match psr.parse(src, msg_hint) {
            ParseResult::Error(e) => ParseResult::Error(e),
            ParseResult::Success(_, p) => ParseResult::Success(self.0.clone(), p),
            ParseResult::Fail(p, _, s) => {
                if !msg_hint {
                    ParseResult::Fail(p, 0, None)
                } else {
                    let lit = self.0.clone();
                    ParseResult::Fail(
                        p,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Failed to find string \"{}\":\n{}",
                                lit,
                                // unwrapping here is a safe operation because
                                // fundamentals always respect `msg_hint`
                                String::from(s.unwrap())
                            )
                        })),
                    )
                }
            }
        }
    }
}

impl Parser for StringLit {}

impl<P: Parser<Output = String>> BitOr<P> for StringLit {
    impl_bitor!(P);
}

impl<P: Parser<Output = String>> Add<P> for StringLit {
    impl_add!(P);
}

/// Parser that matches on a literal string
///
/// This type requires a static reference to a string. For matching with an
/// owned `String`, see [`StringLit`].
///
/// This parser internally uses [`fundamentals::ByteSeq`], so all of its
/// behavior (e.g. always consuming bytes equal to the length of the string)
/// comes from there.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::basics::StrLit;
///
/// let s = String::from("foo-bar");
/// let mut src = Source::new(s.as_bytes());
///
/// assert!(StrLit("foo").parse(&mut src, false).is_success());
/// assert!(StrLit("-bar").parse(&mut src, false).is_success());
/// ```
///
/// [`StringLit`]: struct.StringLit.html
/// [`fundamentals::ByteSeq`]: ../fundamentals/struct.ByteSeq.html
pub struct StrLit(pub &'static str);

impl DynParser for StrLit {
    type Output = &'static str;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<&'static str> {
        match ByteSeq(self.0).parse(src, msg_hint) {
            ParseResult::Error(e) => ParseResult::Error(e),
            ParseResult::Success(_, p) => ParseResult::Success(self.0, p),
            ParseResult::Fail(p, _, s) => {
                if !msg_hint {
                    ParseResult::Fail(p, 0, None)
                } else {
                    let ref_to_static_str = self.0;
                    ParseResult::Fail(
                        p,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Failed to find string \"{}\":\n{}",
                                ref_to_static_str,
                                // unwrapping here is a safe operation because
                                // fundamentals always respect `msg_hint`
                                String::from(s.unwrap())
                            )
                        })),
                    )
                }
            }
        }
    }
}

impl Parser for StrLit {}

impl<P: Parser<Output = &'static str>> BitOr<P> for StrLit {
    impl_bitor!(P);
}

impl<P: Parser<Output = &'static str>> Add<P> for StrLit {
    impl_add!(P);
}

/// Parser that matches a literal unicode character
///
/// This type is constructed with the associated [`char_lit`] function. It is
/// optimized so that matching an ASCII character is no more expensive than
/// matching the byte literal corresponding to that character.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::basics::char_lit;
///
/// let s = "a☺é";
/// let mut src = Source::new(s.as_bytes());
///
/// assert!(char_lit('a').parse(&mut src, false).is_success());
/// assert!(char_lit('☺').parse(&mut src, false).is_success());
/// assert!(char_lit('é').parse(&mut src, false).is_success());
/// ```
///
/// Note that because characters are not all encoded with the same width, it
/// cannot be assumed that failing to parse a character will still consume a
/// full character - more often than not, this will be something that must be
/// backtracked. This is due to the fact that this parser will only consume as
/// many bytes as it expects.
///
/// [`char_lit`]: fn.char_lit.html
#[derive(Clone, Debug)]
pub struct CharLit(CharLitInner);

// This separation exists only to prevent the enum variants from being public
#[derive(Clone, Debug)]
enum CharLitInner {
    Ascii(u8),
    NonAscii(char, ByteSeq<Box<[u8]>>),
}

/// Constructs the [`CharLit`] parser for a given character
///
/// [`CharLit`]: struct.CharLit.html
pub fn char_lit(c: char) -> CharLit {
    let inner = if c.is_ascii() {
        CharLitInner::Ascii(u8::try_from(c as u32).unwrap())
    } else {
        let mut bs = [0u8; 4];

        let psr = ByteSeq(Vec::from(c.encode_utf8(&mut bs).as_bytes()).into_boxed_slice());
        CharLitInner::NonAscii(c, psr)
    };

    CharLit(inner)
}

impl DynParser for CharLit {
    type Output = char;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<char> {
        match &self.0 {
            &CharLitInner::Ascii(b) => {
                match ByteLit(b).parse(src, msg_hint) {
                    ParseResult::Error(e) => ParseResult::Error(e),
                    ParseResult::Success(_, p) => ParseResult::Success(b as char, p),
                    ParseResult::Fail(p, _, s) => {
                        if !msg_hint {
                            ParseResult::Fail(p, 0, None)
                        } else {
                            ParseResult::Fail(
                                p,
                                0,
                                Some(LazyString::new(move || {
                                    format!(
                                        "Failed to find character '{}':\n{}",
                                        b as char,
                                        String::from(s.unwrap())
                                    )
                                })),
                            )
                        }
                    },
                }
            },
            CharLitInner::NonAscii(lit, psr) => {
                match psr.parse(src, msg_hint) {
                    ParseResult::Error(e) => ParseResult::Error(e),
                    ParseResult::Success(_, p) => ParseResult::Success(*lit, p),
                    ParseResult::Fail(p, _, s) => {
                        if !msg_hint {
                            ParseResult::Fail(p, 0, None)
                        } else {
                            let lit = *lit;
                            ParseResult::Fail(
                                p,
                                0,
                                Some(LazyString::new(move || {
                                    format!(
                                        "Failed to find character '{}':\n{}",
                                        lit,
                                        String::from(s.unwrap())
                                        )
                                })),
                            )
                        }
                    },
                }
            },
        }
    }
}

impl Parser for CharLit {}

impl<P: Parser<Output = char>> BitOr<P> for CharLit {
    impl_bitor!(P);
}

impl<P: Parser<Output = char>> Add<P> for CharLit {
    impl_add!(P);
}

/// Parser that matches any unicode character in the given range
///
/// This type is construted with the associated [`char_range`] function.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::basics::{CharRange, char_range};
///
/// let s = String::from("é☺♥");
/// let mut src = Source::new(s.as_bytes());
///
/// let psr = char_range('a', '♋');
///
/// assert!(psr.parse(&mut src, false).is_success());
/// assert!(psr.parse(&mut src, false).is_success());
/// assert!(psr.parse(&mut src, false).is_fail());
/// ```
///
/// # Notes on failure and consumption
///
/// This parser will not return an error if what it reads isn't valid UTF-8; it
/// will instead just fail, giving that information through the error message.
///
/// Additionally, the number of bytes that this parser consumes is not static -
/// assuming that the input text is valid UTF-8, it will only consume a single
/// unicode scalar value, whether that is an ASCII letter or an accent
/// modifier. In the case of successful (or failed) parses of valid UTF-8, this
/// parser can be chained as normal. There are no guarantees made for invalid
/// UTF-8 sequences aside from failure.
///
/// [`char_range`]: fn.char_range.html
// TODO: This could be optimized, but given the relative infrequency of using
// this *particular* parser, that's likely something best left for another time
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CharRange {
    lower: u32,
    upper: u32,
}

/// Constructs the [`CharRange`] parser with the given range
///
/// [`CharRange`]: struct.CharRange.html
pub fn char_range(lower: char, upper: char) -> CharRange {
    CharRange {
        lower: lower as u32,
        upper: upper as u32,
    }
}

impl DynParser for CharRange {
    type Output = char;
    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<char> {
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
        let (first, pos) = match src.read_single() {
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
        match src.read_many(req_len - 1) {
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

impl Parser for CharRange {}

impl<P: Parser<Output = char>> BitOr<P> for CharRange {
    impl_bitor!(P);
}

impl<P: Parser<Output = char>> Add<P> for CharRange {
    impl_add!(P);
}

#[cfg(test)]
mod tests {
    use crate::{source::Source, DynParser};

    #[test]
    fn string_lit() {
        let s = String::from("foo bar string");
        let mut src = Source::new(s.as_bytes());
        assert!(super::StringLit(String::from("foo")).parse(&mut src, false)
                .is_success());
        assert!(super::StringLit(String::from("abcde")).parse(&mut src, false)
                .is_fail());
        assert!(super::StringLit(String::from("string")).parse(&mut src, false)
                .is_success());
    }

    #[test]
    fn str_lit() {
        let s = String::from("foo bar string");
        let mut src = Source::new(s.as_bytes());
        assert!(super::StrLit("foo").parse(&mut src, false)
                .is_success());
        assert!(super::StrLit("abcde").parse(&mut src, false)
                .is_fail());
        assert!(super::StrLit("string").parse(&mut src, false)
                .is_success());
    }

    #[test]
    fn char_lit() {
        let s = "ab☺é";
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
