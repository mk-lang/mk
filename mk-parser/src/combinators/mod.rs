//! Definitions for parser combinators
//!
//! The contents of this module will usually be `use`d directly, without
//! referring to each by `combinators::foo`, as that would be overly verbose.
//!
//! There are examples of general usage in the crate root, in addition to those
//! provided for each type.

mod any;
pub use any::{any, DynAny, Either, IntoAny};
mod all;
pub use all::{all, Chain, DynAll, IntoAll};

use crate::{source::Source, utils::LazyString, DynParser, ParseResult, Parser};

#[cfg(feature = "bnf-syntax")]
use std::ops::{Add, BitOr};

/// Parser that wraps the output of another parser with a function
///
/// This parser is constructed with the [`map`] method provided by the
/// `Parser` trait.
///
/// # Examples
///
/// ```
/// use mk_parser::{Parser, DynParser, ParseResult, source::Source};
/// use mk_parser::fundamentals::TakeWhile;
///
/// let s = "word! plus more";
/// let mut src = Source::new(s.as_bytes());
///
/// let psr = TakeWhile(|b| b.is_ascii_alphanumeric())
///     .map(|bs| String::from_utf8(bs).unwrap());
///
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "word");
/// ```
///
/// [`map`]: ../trait.Parser.html#method.map
pub struct Map<P, F, T>
where
    P: Parser,
    F: 'static + Fn(P::Output) -> T,
{
    pub(super) psr: P,
    pub(super) func: F,
}

impl<P, F, T> DynParser for Map<P, F, T>
where
    P: Parser,
    F: 'static + Fn(P::Output) -> T,
{
    type Output = T;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<T> {
        match self.psr.parse(src, msg_hint) {
            ParseResult::Success(t, pos) => ParseResult::Success((self.func)(t), pos),
            ParseResult::Fail(pos, i, m) => ParseResult::Fail(pos, i, m),
            ParseResult::Error(e) => ParseResult::Error(e),
        }
    }
}

// We could write a custom implementation for the map method here, but the
// marginal benefits are likely inconsequential.
impl<P, F, T> Parser for Map<P, F, T>
where
    P: Parser,
    F: 'static + Fn(P::Output) -> T,
{
}

#[cfg(feature = "bnf-syntax")]
impl<P, F, T, P2> BitOr<P2> for Map<P, F, T>
where
    P: Parser,
    F: 'static + Fn(P::Output) -> T,
    P2: Parser<Output = T>,
{
    impl_bitor!(P2);
}

#[cfg(feature = "bnf-syntax")]
impl<P, F, T, P2> Add<P2> for Map<P, F, T>
where
    P: Parser,
    F: 'static + Fn(P::Output) -> T,
    P2: Parser<Output = T>,
{
    impl_add!(P2);
}

/// Parser combinator for repeated matches of a parser
///
/// This parser is constructed with the [`repeat`] method provided by the
/// `Parser` trait.
///
/// # Examples
///
/// Matching some number of occurances of "foo":
/// ```
/// use mk_parser::{Parser, DynParser, ParseResult, source::Source};
/// use mk_parser::basics::StrLit;
///
/// let s = "foo foo bar foo bar";
/// let mut src = Source::new(s.as_bytes());
///
/// let psr = StrLit("foo ").repeat(1, None);
///
/// // We're given both of the matches
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, ["foo ", "foo "]);
///
/// // getting "bar" fails, but only tries once
/// assert!(psr.parse(&mut src, false).is_fail());
///
/// // getting "foo" once more is just fine, because the failure from "bar"
/// // consumed just enough bytes to put us at the start of the next "foo"
/// assert!(psr.parse(&mut src, false).is_success());
/// ```
///
/// # Notes on failure and consumption
///
/// This parser can fail in either of two ways. Firstly, if the base parser
/// fails a match before we've found the minimum number of matches, this
/// parser will fail. Additionally, if the minimum number of matches **has**
/// been met, but the base parser fails with a failure level not equal to `0`,
/// that will cause a failure here as well, with the failure level decremented
/// once. Also of note is that `msg_hint` will be ignored if the failure level
/// is not zero.
///
/// If this parser fails, the behavior of the number of bytes it will have
/// consumed is entirely dictated by the base parser. As shown in the example
/// above, constant-size parsers will fail in constant-size blocks. Others may
/// not abide by the same rules. Whether or not the parser has found the
/// minimum number of matches does not affect this.
///
/// If the parser is successful, it will only have consumed the bytes necessary
/// for the successful parses of each repetition. The terminating failure (if
/// there is one) has no effect.
///
/// [`repeat` method]: ../trait.Parser.html#method.repeat
/// [`repeat`]: fn.repeat.html
#[derive(Debug, Clone)]
pub struct Repeat<P>
where
    P: Parser,
{
    pub(super) lower: usize,
    pub(super) upper: Option<usize>,
    pub(super) psr: P,
}

impl<P> DynParser for Repeat<P>
where
    P: Parser,
{
    type Output = Vec<P::Output>;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Self::Output> {
        // `pos` is used in various places throughout this function
        let pos = src.pos();

        // If the lower bound is greater than the upper bound, it's not
        // possible to parse. Additionally, the logic later requires this to
        // not be the case.
        if self.upper.is_some() && (self.lower > self.upper.unwrap()) {
            if !msg_hint {
                return ParseResult::Fail(pos, 0, None);
            } else {
                let (lower, upper) = (self.lower, self.upper);
                return ParseResult::Fail(
                    pos,
                    0,
                    Some(LazyString::new(move || {
                        format!(
                            "{} Lower bound {:?} > upper bound {:?}",
                            "Failed to match pattern repetition",
                            lower,
                            upper.unwrap()
                        )
                    })),
                );
            }
        }

        let (mut ret, upper) = match self.upper {
            Some(u) => (Vec::with_capacity(u), u),
            None => (Vec::new(), std::usize::MAX),
        };

        for r in 0..self.lower {
            match self.psr.parse(src, msg_hint) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(o, _) => ret.push(o),
                ParseResult::Fail(p, i, m) => {
                    let msg = if !msg_hint {
                        None
                    } else if m.is_some() {
                        let lower = self.lower;
                        Some(LazyString::new(move || {
                            format!(
                                "{} {:?} {} {:?}. From {}:\n{}",
                                "Only matched",
                                r,
                                "times, needed at least",
                                lower,
                                p,
                                String::from(m.unwrap())
                            )
                        }))
                    } else {
                        let lower = self.lower;
                        Some(LazyString::new(move || {
                            format!(
                                "{} {:?} {} {:?} at {} {}.",
                                "Only matched",
                                r,
                                "times, needed at least",
                                lower,
                                p,
                                "without an additional message"
                            )
                        }))
                    };

                    let new_i = match i {
                        0 => 0,
                        _ => i - 1,
                    };

                    return ParseResult::Fail(pos, new_i, msg);
                }
            }
        }

        for r in self.lower..upper {
            src.mark_backtrack();

            match self.psr.parse(src, false) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(o, _) => ret.push(o),
                // If it's an expected error, we already have enough.
                ParseResult::Fail(_, 0, _) => {
                    src.backtrack();
                    src.unmark_backtrack();
                    break;
                }
                ParseResult::Fail(p, i, m) => {
                    src.backtrack();
                    src.unmark_backtrack();

                    return if let Some(m) = m {
                        ParseResult::Fail(
                            pos,
                            i - 1,
                            Some(LazyString::new(move || {
                                format!(
                                    "{} {:?} {}. From {}:\n{}",
                                    "Matched",
                                    r,
                                    "times, higher-order fail encountered",
                                    p,
                                    String::from(m)
                                )
                            })),
                        )
                    } else if msg_hint {
                        ParseResult::Fail(
                            pos,
                            i - 1,
                            Some(LazyString::new(move || {
                                format!(
                                    "{} {:?} {} at {} {}.",
                                    "Matched",
                                    r,
                                    "times, higher-order fail encountered",
                                    p,
                                    "without message"
                                )
                            })),
                        )
                    } else {
                        ParseResult::Fail(pos, i - 1, None)
                    };
                }
            }

            src.unmark_backtrack();
        }

        ParseResult::Success(ret, pos)
    }
}

impl<P: Parser> Parser for Repeat<P> {}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser, P2: Parser<Output = Vec<P::Output>>> BitOr<P2> for Repeat<P> {
    impl_bitor!(P2);
}

#[cfg(feature = "bnf-syntax")]
impl<P: Parser, P2: Parser<Output = Vec<P::Output>>> Add<P2> for Repeat<P> {
    impl_add!(P2);
}

#[cfg(test)]
mod tests {
    use crate::{
        basics::{char_lit, StrLit},
        fundamentals::ByteLit,
        source::Source,
        DynParser, Parser,
    };

    #[test]
    fn map() {
        let s = "f";
        let mut src = Source::new(s.as_bytes());

        let psr = ByteLit(0x66).map(|c| format!("first! {}", c as char));
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "first! f");
    }

    #[test]
    fn repeat() {
        // NOTE: This is a partial test... There's a lot more complicated failure
        // logic within `repeat` that should be tested

        let s = "foofoo...BARBARBAR...";
        let mut src = Source::new(s.as_bytes());

        let foo = StrLit("foo").repeat(2, None);
        let dot = char_lit('.').repeat(0, Some(3));
        let bar = StrLit("BAR").repeat(0, None);

        assert_eq!(foo.parse(&mut src, false).unwrap().0, vec!["foo", "foo"]);
        assert_eq!(dot.parse(&mut src, false).unwrap().0, vec!['.', '.', '.']);
        assert_eq!(
            bar.parse(&mut src, false).unwrap().0,
            vec!["BAR", "BAR", "BAR"]
        );
    }
}
