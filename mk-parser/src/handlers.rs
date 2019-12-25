//! Parser wrappers for changing messages, failure levels, and more
//!
//! These have to do with the meta-information associated with failing to parse
//! a section of the input. The majority of the functionality provided by these
//! parsers can be obtained through the methods on [`Parser`] (see [`name`],
//! [`expect`], and [`require`]), but there are a few features that can only be
//! used through direct usage of the types provided here - specifically
//! [`FailLevel`].
//!
//! [`Parser`]: ../trait.Parser.html#method.
//! [`name`]: ../trait.Parser.html#method.name
//! [`expect`]: ../trait.Parser.html#method.expect
//! [`require`]: ../trait.Parser.html#method.require
//! [`FailLevel`]: struct.FailLevel.html

use crate::{source::Source, utils::LazyString, DynParser, ParseResult, Parser};

#[cfg(feature = "bnf-syntax")]
use std::ops::{Add, BitOr};

/// Modifies the error message of the core parser
///
/// If the inner parser provides a failure message, `FailWith` will apply the
/// function to that message to produce a new one. If the parser does not give
/// a failure message, `FailWith` will provide `default` - assuming that the
/// `msg_hint` argument to [`DynParser::parse`] is true, of course.
///
/// `FailWith` will abide by the same standards as the [`combinators`]: it will
/// generally respect `msg_hint`, but will override to provide an error message
/// if the failure level is non-zero **and** a failure message was provided.
///
/// The function is required to implement `Clone` because the parser that this
/// wraps could be called many times, but we still want to maintain the laziness
/// of our error messages - hence why we need to be able to produce multiple
/// copies of the function.
///
/// This type can also be constructed with the [`fail_with`] function.
///
/// [`DynParser::parse`]: ../trait.DynParser.html#tymethod.parse
/// [`combinators`]: ../combinators/index.html
/// [`fail_with`]: fn.fail_with.html
pub struct FailWith<P, F>
where
    F: 'static + Clone + Fn(String) -> String,
    P: Parser,
{
    pub psr: P,
    pub default: Option<String>,
    pub func: F,
}

/// A function for constructing [`FailWith`]
///
/// [`FailWith`]: struct.FailWith.html
pub fn fail_with<P, F>(psr: P, default: Option<String>, func: F) -> FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
{
    FailWith { psr, func, default }
}

impl<P, F> DynParser for FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
{
    type Output = P::Output;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<P::Output> {
        match self.psr.parse(src, msg_hint) {
            ParseResult::Error(e) => ParseResult::Error(e),
            ParseResult::Success(t, p) => ParseResult::Success(t, p),
            ParseResult::Fail(pos, lvl, m) => {
                let msg = if m.is_some() && (msg_hint || lvl != 0) {
                    let f = self.func.clone();
                    Some(LazyString::new(move || f(m.unwrap().into())))
                } else if msg_hint {
                    self.default.clone().map(|m| LazyString::new(|| m))
                } else {
                    None
                };

                ParseResult::Fail(pos, lvl, msg)
            }
        }
    }
}

impl<P, F> Parser for FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
{
}

#[cfg(feature = "bnf-syntax")]
impl<P, F, P2> BitOr<P2> for FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
    P2: Parser<Output = P::Output>,
{
    impl_bitor!(P2);
}

#[cfg(feature = "bnf-syntax")]
impl<P, F, P2> Add<P2> for FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
    P2: Parser<Output = P::Output>,
{
    impl_add!(P2);
}

/// Wraps failure messages with the given name
///
/// This parser is usually constructed with the [`Parser::name`] method, but of
/// course you can instantiate it yourself.
///
/// Typial usage will be so to name complex combinations of parsers so that
/// failure can be easily recognized.
///
/// [`Parser::name`]: ../trait.Parser.html#method.name
pub struct Named<P>
where
    P: Parser,
{
    pub psr: P,
    pub name: String,
}

impl<P> DynParser for Named<P>
where
    P: Parser,
{
    type Output = P::Output;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<P::Output> {
        match self.psr.parse(src, msg_hint) {
            ParseResult::Error(e) => ParseResult::Error(e),
            ParseResult::Success(t, p) => ParseResult::Success(t, p),
            ParseResult::Fail(pos, lvl, None) => {
                let name = self.name.clone();
                ParseResult::Fail(
                    pos,
                    lvl,
                    Some(LazyString::new(move || format!("Failed to parse {}", name))),
                )
            }
            ParseResult::Fail(pos, lvl, Some(m)) => {
                let name = self.name.clone();
                ParseResult::Fail(
                    pos,
                    lvl,
                    Some(LazyString::new(move || {
                        format!("Failed to parse {}: {}", name, String::from(m))
                    })),
                )
            }
        }
    }
}

impl<P: Parser> Parser for Named<P> {}

#[cfg(feature = "bnf-syntax")]
impl<P, P2> BitOr<P2> for Named<P>
where
    P: Parser,
    P2: Parser<Output = P::Output>,
{
    impl_bitor!(P2);
}

#[cfg(feature = "bnf-syntax")]
impl<P, P2> Add<P2> for Named<P>
where
    P: Parser,
    P2: Parser<Output = P::Output>,
{
    impl_add!(P2);
}

/// Modifies the failure level of the parser with the given function
///
/// The fields of the struct are made public to allow simpler explanation here,
/// in addition to greater freedom for usage. Note that this parser will
/// typically be constructed with the associated [`fail_level`] function in
/// this module.
///
/// For more information on failure levels, see [`ParseResult::Fail`].
///
/// [`fail_level`]: fn.fail_level.html
/// [`ParseResult::Fail`]: ../enum.ParseResult.html#failure-level
pub struct FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
{
    pub psr: P,
    pub lvl: F,
}

/// Constructs the [`FailLevel`] parser with the given fields
///
/// This simply exists as a more syntactically elegant way of constructing
/// `FailLevel` for simpler functions. This is the preferred method.
///
/// [`FailLevel`]: struct.FailLevel.html
pub fn fail_level<P, F>(psr: P, lvl: F) -> FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
{
    FailLevel { psr, lvl }
}

impl<P, F> DynParser for FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
{
    type Output = P::Output;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<P::Output> {
        match self.psr.parse(src, msg_hint) {
            ParseResult::Success(t, p) => ParseResult::Success(t, p),
            ParseResult::Error(e) => ParseResult::Error(e),
            ParseResult::Fail(pos, lvl, m) => ParseResult::Fail(pos, (self.lvl)(lvl), m),
        }
    }
}

impl<P, F> Parser for FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
{
}

#[cfg(feature = "bnf-syntax")]
impl<P, F, P2> BitOr<P2> for FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
    P2: Parser<Output = P::Output>,
{
    impl_bitor!(P2);
}

#[cfg(feature = "bnf-syntax")]
impl<P, F, P2> Add<P2> for FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
    P2: Parser<Output = P::Output>,
{
    impl_add!(P2);
}

#[cfg(test)]
mod tests {
    use crate::{fundamentals, source::Source, DynParser};

    #[test]
    fn fail_with_default() {
        let s = "a b c d, e f g ... ";
        let mut src = Source::new(s.as_bytes());

        let psr = super::fail_with(fundamentals::fail::<()>(), Some("foo".into()), |_| {
            "bar".into()
        });

        assert!(psr.parse(&mut src, false).unwrap_fail().2.is_none());
        assert_eq!(
            psr.parse(&mut src, true)
                .unwrap_fail()
                .2
                .map(String::from)
                .unwrap(),
            "foo"
        );
    }

    #[test]
    fn fail_with_func() {
        let s = "a b c d, e f g ... ";
        let mut src = Source::new(s.as_bytes());

        let psr = super::fail_with(
            super::fail_with(fundamentals::fail::<()>(), Some("foo".into()), |_| {
                "bar".into()
            }),
            Some("baz".into()),
            |m| format!("{}!", m),
        );

        assert!(psr.parse(&mut src, false).unwrap_fail().2.is_none());
        assert_eq!(
            psr.parse(&mut src, true)
                .unwrap_fail()
                .2
                .map(String::from)
                .unwrap(),
            "foo!"
        );
    }

    /*
    #[test]
    fn named() {
        compile_error!("Need a test for `Named`");
    }

    #[test]
    fn fail_level() {
        compile_error!("Need a test for `FailLevel`");
    }
    */
}
