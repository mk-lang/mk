//! The fundamental `Parser`s, used for direct interaction with the `Source`
//!
//! The [`Parser`]s defined in this module are not typically used outside of
//! the internal definitions of other parsers in this crate, but you are free
//! to have a look. They may be useful if you are looking to do lower-level
//! parsing operations.
//!
//! This module consists only of parser definitions. Some have an associated
//! function to construct them.
//!
//! [`Parser`]: ../trait.Parser.html

use crate::{
    source::{ReadMany, ReadSingle, Source},
    utils::LazyString,
    DynParser, ParseResult, Parser,
};

use std::{
    borrow::Borrow,
    marker::PhantomData,
};

#[cfg(feature = "bnf-syntax")]
use std::ops::{Add, BitOr};

////////////////////////////////////////////////////////////

// Helper function for providing failure messages

fn byte_name(b: u8) -> String {
    if b.is_ascii_graphic() {
        ['\'', b as char, '\''].iter().collect()
    } else {
        format!("byte value {:#x}", b)
    }
}

////////////////////////////////////////////////////////////

/// Dummy parser that always succeeds
///
/// This parser can be thought of as one of the fundamental mathematical
/// objects necessary of parser combinators. Outside of that, it doesn't really
/// have a practial use, except for testing.
///
/// # Example
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source, utils::Pos};
/// use mk_parser::fundamentals::Succeed;
///
/// let text = "foobar";
/// let mut src = Source::new(text.as_bytes());
///
/// let psr = Succeed;
/// assert_eq!(psr.parse(&mut src, false).unwrap(), ((), Pos::from((1, 1))));
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Succeed;

impl DynParser for Succeed {
    type Output = ();

    fn parse(&self, src: &mut Source, _msg_hint: bool) -> ParseResult<()> {
        ParseResult::Success((), src.pos())
    }
}

impl Parser for Succeed {}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser<Output = ()>> BitOr<P> for Succeed {
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser<Output = ()>> Add<P> for Succeed {
    impl_add!(P);
}

/// Dummy parser that always fails
///
/// In much the same way that [`Succeed`] always succeeds, this parser will
/// always fail, producing a `ParseResult::Fail`, where the second and third
/// positions in the tuple are given by `lvl` and `msg`.
///
/// In a similar fashion to `Succeed`, this parser doesn't have much of a use
/// case outside of testing, but it's here because it is still a kind of
/// fundamental parser in the mathematical sense.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::fundamentals::{Fail, fail};
///
/// let text = "foobar";
/// let mut src = Source::new(text.as_bytes());
///
/// let psr: Fail<()> = fail();
/// assert!(psr.parse(&mut src, false).is_fail());
/// ```
/// And for more advanced cases:
/// ```
/// # use mk_parser::{DynParser, ParseResult, source::Source};
/// # use mk_parser::fundamentals::Fail;
/// # let text = "foobar";
/// # let mut src = Source::new(text.as_bytes());
/// let psr: Fail<()> = Fail {
///     lvl: 1,
///     msg: Some("failed!".into()),
///     .. Fail::default()
/// };
///
/// let res = psr.parse(&mut src, true);
/// assert!(res.is_fail());
/// let (_, lvl, msg) = res.unwrap_fail();
/// assert_eq!(lvl, 1);
/// assert_eq!(String::from(msg.unwrap()), "failed!");
/// ```
///
/// Typically, usage of this type will be done with the [`fail`] function, but
/// anything more than bare-bones usage requires instantiating the struct
/// yourself.
///
/// As such, if you do require the more advanced functionality (unlikely unless
/// you are a test), it may be worth looking at the implementation of `Default`
/// for it. While not strictly required, it is stongly recommended that you use
/// it instead of instantiating the final field, `_marker`, by yourself. More
/// information can be found in its doc comment. As well as a **forwards
/// compatibility note**.
///
/// [`Succeed`]: struct.Succeed.html
/// [`fail`]: fn.fail.html
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fail<T> {
    /// Sets the level to fail with - the second field in [`ParseResult::Fail`]
    ///
    /// Defaults to `0`. The meaning of this value can be found in the
    /// documentation of [`ParseResult`].
    ///
    /// [`ParseResult::Fail`]: ../enum.ParseResult.html#variant.Fail
    /// [`ParseResult`]: ../enum.ParseResult.html
    pub lvl: i64,

    /// Optionally gives a message to fail with
    ///
    /// This directly corresponds to the message field of [`ParseResult::Fail`],
    /// and will - by default - respect the `msg_hint` argument to
    /// [`DynParser::parse()`]. This can be changed with `ign_hint` below.
    ///
    /// [`ParseResult::Fail`]: ../enum.ParseResult.html#variant.Fail
    /// [`DynParser::parse()`]: ../trait.DynParser.html#tymethod.parse
    pub msg: Option<String>,

    /// Dictates whether to override `msg_hint` and return a message anyways
    ///
    /// This will obviously have no effect if `msg` is `None`.
    ///
    /// This is largely made available for testing.
    pub ign_hint: bool,

    /// A marker to preserve the output type. This will be deprecated.
    ///
    /// Because all generic parameters of a struct must be used within that
    /// struct, we need some way to preserve `T`, so we do that here.
    ///
    /// It will often be easier to instead fill from `Default::default()`, so
    /// it is recommended to do that. The second example above demonstrates
    /// this.
    ///
    /// # Forwards compatibility
    ///
    /// This field will be removed once the [never type] is stabilized, which
    /// looks to be relatively soon, in addition to the type parameter `T`; the
    /// implementation of `DynParser` will switch to using `!` as its output
    /// type.
    ///
    /// [never type]: https://doc.rust-lang.org/std/primitive.never.html
    pub _marker: PhantomData<T>,
}

/// Returns the default [`Fail`] parser
///
/// Example usage can be found [here].
///
/// [`Fail`]: struct.Fail.html
/// [here]: struct.Fail.html#examples
pub fn fail<T>() -> Fail<T> {
    Fail::default()
}

impl<T> Default for Fail<T> {
    fn default() -> Self {
        Fail {
            lvl: 0,
            msg: None,
            ign_hint: false,
            _marker: PhantomData,
        }
    }
}

// TODO: When the never type gets stabilized, change the output type to `!` and
// remove the generic type parameter.
impl<T> DynParser for Fail<T> {
    type Output = T;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<T> {
        if let (true, Some(m)) = (msg_hint || self.ign_hint, self.msg.as_ref()) {
            let m = m.clone();
            ParseResult::Fail(src.pos(), self.lvl, Some(LazyString::new(move || m)))
        } else {
            ParseResult::Fail(src.pos(), self.lvl, None)
        }
    }
}

impl<T> Parser for Fail<T> {}

#[cfg(feature = "bnf-syntax")]
impl<T, P: Parser<Output = T>> BitOr<P> for Fail<T> {
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<T, P: Parser<Output = T>> Add<P> for Fail<T> {
    impl_add!(P);
}

/// Parser that takes bytes while a predicate is met
///
/// # Examples
///
/// Constructing the [`word`] parser ourself:
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::fundamentals::TakeWhile;
///
/// let s = "more than one word";
/// let mut src = Source::new(s.as_bytes());
///
/// let psr = TakeWhile(|b| b.is_ascii_alphabetic());
/// let res = psr.parse(&mut src, false);
/// assert_eq!(res.unwrap().0, "more".as_bytes());
/// ```
///
/// [`word`]: ../basics/fn.word.html
#[derive(Copy, Clone, Debug)]
pub struct TakeWhile<F: Fn(u8) -> bool>(pub F);

impl<F: Fn(u8) -> bool> DynParser for TakeWhile<F> {
    type Output = Vec<u8>;

    fn parse(&self, src: &mut Source, _msg_hint: bool) -> ParseResult<Vec<u8>> {
        match src.read_while(|b, _| self.0(b)) {
            ReadMany::Error(e) => ParseResult::Error(e),
            ReadMany::Bytes(bs, pos) => ParseResult::Success(bs, pos),
            ReadMany::EOF(_) => {
                panic!("Unexpected EOF from calling `Source::read_while`");
            }
        }
    }
}

impl<F: Fn(u8) -> bool> Parser for TakeWhile<F> {}

#[cfg(feature = "bnf-syntax")]
impl<F, P> BitOr<P> for TakeWhile<F>
where
    F: Fn(u8) -> bool,
    P: Parser<Output = <Self as DynParser>::Output>,
{
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<F, P> Add<P> for TakeWhile<F>
where
    F: Fn(u8) -> bool,
    P: Parser<Output = <Self as DynParser>::Output>,
{
    impl_add!(P);
}

/// Parser that matches exactly on the given byte
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::fundamentals::ByteLit;
///
/// let mut src = Source::new(&[0x66_u8, 0x6F, 0x6F] as &[u8]);
///
/// let res = ByteLit(0x66).parse(&mut src, false);
/// assert!(res.is_success());
///
/// let res = ByteLit(0x6F).parse(&mut src, false);
/// assert!(res.is_success());
///
/// let res = ByteLit(0x60).parse(&mut src, false);
/// assert!(res.is_fail());
/// ```
/// Please note that this is not the recommended way to match a string. For
/// that, see [`StringLit`].
///
/// [`StringLit`]: ../basics/struct.StringLit.html
#[repr(transparent)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ByteLit(pub u8);

impl DynParser for ByteLit {
    type Output = u8;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<u8> {
        match src.read_single() {
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

impl Parser for ByteLit {}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser<Output = u8>> BitOr<P> for ByteLit {
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser<Output = u8>> Add<P> for ByteLit {
    impl_add!(P);
}

/// Parser that matches on any byte within the given range, inclusive
///
/// The first element of the tuple gives the lower bound; the second gives the
/// upper bound.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::fundamentals::ByteRange;
///
/// let mut src = Source::new(&[0x61_u8, 0x63, 0x65, 0x67] as &[u8]);
///
/// let psr = ByteRange(0x62, 0x65);
///
/// // 0x61
/// assert!(psr.parse(&mut src, false).is_fail());
///
/// // 0x63
/// assert!(psr.parse(&mut src, false).is_success());
///
/// // 0x65
/// assert!(psr.parse(&mut src, false).is_success());
///
/// // 0x67
/// assert!(psr.parse(&mut src, false).is_fail());
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ByteRange(pub u8, pub u8);

impl DynParser for ByteRange {
    type Output = u8;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<u8> {
        match src.read_single() {
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
                                byte_name(cloned.0),
                                byte_name(cloned.1)
                            )
                        })),
                    )
                } else {
                    ParseResult::Fail(pos, 0, None)
                }
            }
            ReadSingle::Byte(b, pos) => {
                if b >= self.0 && b <= self.1 {
                    ParseResult::Success(b, pos)
                } else if msg_hint {
                    let cloned = *self;
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected a byte in range {} to {}, found {}",
                                byte_name(cloned.0),
                                byte_name(cloned.1),
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

impl Parser for ByteRange {}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser<Output = u8>> BitOr<P> for ByteRange {
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser<Output = u8>> Add<P> for ByteRange {
    impl_add!(P);
}

/// Parser that matches exactly on a given sequence of bytes
///
/// The generic parameter allows the flexibility to use many types for the
/// sequence, notably `String`s and `Vec<u8>` (along with their borrowed
/// counterparts, `&str` and `&[u8]`).
///
/// Note that this parser will always consume exactly as many bytes as is
/// expected.
///
/// # Example
///
/// ```
/// use mk_parser::{DynParser, ParseResult, source::Source};
/// use mk_parser::fundamentals::ByteSeq;
///
/// let s = "foobarfoo";
/// let mut src = Source::new(s.as_bytes());
///
/// let psr = ByteSeq("foo");
///
/// // getting the first "foo"
/// assert!(psr.parse(&mut src, false).is_success());
///
/// // we fail to match, but still consume the three bytes from "bar"
/// assert!(psr.parse(&mut src, false).is_fail());
///
/// // getting the second foo
/// assert!(psr.parse(&mut src, false).is_success());
/// ```
#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteSeq<S>(pub S)
where
    S: AsRef<[u8]> + ToOwned,
    S::Owned: 'static;

impl<S> DynParser for ByteSeq<S>
where
    S: AsRef<[u8]> + ToOwned,
    S::Owned: 'static,
{
    type Output = Vec<u8>;

    // TODO: Determine whether it's faster to make incrementally compare vs.
    // get the whole set
    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Vec<u8>> {
        match src.read_many(self.0.as_ref().len()) {
            ReadMany::Error(e) => ParseResult::Error(e),
            ReadMany::EOF(pos) => {
                if msg_hint {
                    let cloned = self.0.to_owned();
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected byte sequence {:?}, found EOF",
                                cloned.borrow().as_ref().iter().map(|b| format!("{}", b))
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
                    let cloned = self.0.to_owned();
                    ParseResult::Fail(
                        pos,
                        0,
                        Some(LazyString::new(move || {
                            format!(
                                "Expected byte sequence {:?}, found {:?}",
                                cloned.borrow().as_ref().iter().map(|b| format!("{}", b)),
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

impl<S> Parser for ByteSeq<S>
where
    S: AsRef<[u8]> + ToOwned,
    S::Owned: 'static,
{
}

#[cfg(feature = "bnf-syntax")]
impl<S, P> BitOr<P> for ByteSeq<S>
where
    S: AsRef<[u8]> + ToOwned,
    S::Owned: 'static,
    P: Parser<Output = Vec<u8>>,
{
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<S, P> Add<P> for ByteSeq<S>
where
    S: AsRef<[u8]> + ToOwned,
    S::Owned: 'static,
    P: Parser<Output = Vec<u8>>,
{
    impl_add!(P);
}

#[cfg(test)]
mod tests {
    use crate::source::Source;
    use crate::utils::Pos;
    use crate::DynParser;

    #[test]
    fn success() {
        let s = "foobar";
        let mut src = Source::new(s.as_bytes());
        let res = super::Succeed.parse(&mut src, false);
        assert!(!res.is_error());
        assert!(!res.is_fail());
        assert_eq!(res.unwrap().1, Pos::from((1, 1)));
    }

    #[test]
    fn fail() {
        let s = "foobar";
        let mut src = Source::new(s.as_bytes());

        let mut test = |lvl: i64, msg: Option<String>, ign_hint: bool, msg_hint: bool| {
            let debug_str = format!(
                "DEBUG: lvl: {}, msg: {:?}, ign_hint: {}, msg_hint: {}",
                lvl, msg, ign_hint, msg_hint,
            );

            let psr: super::Fail<()> = super::Fail {
                lvl,
                msg: msg.clone(),
                ign_hint,
                ..Default::default()
            };

            let res = psr.parse(&mut src, msg_hint);
            assert!(!res.is_error(), "{}", debug_str);
            assert!(!res.is_success(), "{}", debug_str);

            let (pos, l, m) = res.unwrap_fail();
            assert_eq!(pos, Pos::from((1, 1)), "{}", debug_str);
            assert_eq!(l, lvl, "{}", debug_str);

            // The first case is the only case where the outputs don't match
            if msg.is_some() && !msg_hint && !ign_hint {
                assert!(m.is_none(), "{}", debug_str);
            } else {
                assert_eq!(msg, m.map(String::from), "{}", debug_str);
            }
        };

        for &lvl in [-2, 0, 2].into_iter() {
            for msg in [None, Some(String::from("sample msg"))].into_iter() {
                for &ign_hint in [false, true].into_iter() {
                    for &msg_hint in [false, true].into_iter() {
                        test(lvl, msg.clone(), ign_hint, msg_hint);
                    }
                }
            }
        }
    }

    #[test]
    fn take_while() {
        // Sample of getting a word
        let s = "single word";
        let mut src = Source::new(s.as_bytes());

        let psr = super::TakeWhile(|b| b.is_ascii_alphabetic());
        let res = psr.parse(&mut src, false);
        assert!(!res.is_error());
        assert!(!res.is_fail());
        assert_eq!(res.unwrap().0, "single".as_bytes());
    }

    #[test]
    fn byte_lit() {
        // TODO: Test position as well
        let s = vec![0x00u8, 0x61, 0x62, 0x63, 0xFF, 0xFE];
        let mut src1 = Source::new(s.as_slice());
        let mut src2 = Source::new(s.as_slice());

        let tab = vec![0x00u8, 0x50, 0x62, 0x63, 0xFF, 0xFF];
        for (&b, &sb) in tab.iter().zip(s.iter()) {
            let psr = super::ByteLit(b);

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
            let psr = super::ByteRange(lower, upper);

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
            let psr = super::ByteSeq(seq.clone());
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
}
