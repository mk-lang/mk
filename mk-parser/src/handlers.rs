//! Parser wrappers for changing messages, failure levels, and more
// TODO-DOC

use crate::{
    source::Source,
    utils::LazyString,
    DynParser, ParseResult, Parser,
};

use std::ops::{BitOr, Add};

// TODO-DOC: Modifies the error message
pub struct FailWith<P, F>
where
    F: 'static + Clone + Fn(String) -> String,
    P: Parser,
{
    psr: P,
    func: F,
    default: Option<String>,
}

// TODO-DOC
// Will also need a note explaining why `Clone` is necessary here -
// fundamentally, it's because we need to construct the `LazyString`
pub fn fail_with<P, F>(psr: P, default: Option<String>, func: F) -> FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
{
    FailWith {
        psr,
        func,
        default,
    }
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
            ParseResult::Fail(pos, lvl, None) => {
                if let Some(m) = self.default.as_ref() {
                    let m = m.clone();
                    ParseResult::Fail(pos, lvl, Some(LazyString::new(move || m)))
                } else {
                    ParseResult::Fail(pos, lvl, None)
                }
            }
            ParseResult::Fail(pos, lvl, Some(m)) => {
                let f = self.func.clone();
                ParseResult::Fail(pos, lvl, Some(LazyString::new(move || f(String::from(m)))))
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

impl<P, F, P2> BitOr<P2> for FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
    P2: Parser<Output = P::Output>,
{
    impl_bitor!(P2);
}


impl<P, F, P2> Add<P2> for FailWith<P, F>
where
    P: Parser,
    F: 'static + Clone + Fn(String) -> String,
    P2: Parser<Output = P::Output>,
{
    impl_add!(P2);
}

// TODO-DOC
// The main difference between this and `fail_with` is that we allow greater
// flexibility here
pub struct Named<P>
where
    P: Parser,
{
    psr: P,
    name: String,
}

// TODO-DOC
pub fn named<P>(psr: P, name: String) -> Named<P>
where
    P: Parser,
{
    Named {
        psr,
        name,
    }
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

impl<P, P2> BitOr<P2> for Named<P>
where
    P: Parser,
    P2: Parser<Output = P::Output>
{
    impl_bitor!(P2);
}

impl<P, P2> Add<P2> for Named<P>
where
    P: Parser,
    P2: Parser<Output = P::Output>
{
    impl_add!(P2);
}

// TODO-DOC: Sets the failure level of the parser
// ** "sets" is bad phrasing - "wraps"/"modifies" is better
pub struct FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
{
    psr: P,
    lvl: F,
}

pub fn fail_level<P, F>(psr: P, lvl: F) -> FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
{
    FailLevel {
        psr,
        lvl,
    }
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
{}

impl<P, F, P2> BitOr<P2> for FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
    P2: Parser<Output = P::Output>,
{
    impl_bitor!(P2);
}

impl<P, F, P2> Add<P2> for FailLevel<P, F>
where
    P: Parser,
    F: Fn(i64) -> i64,
    P2: Parser<Output = P::Output>,
{
    impl_add!(P2);
}

/*
#[cfg(test)]
mod tests {
    #[test]
    fn fail_with() {
        compile_error!("Need a test for `FailWith`");
    }

    #[test]
    fn named() {
        compile_error!("Need a tset for `Named`");
    }

    #[test]
    fn fail_level() {
        compile_error!("Need a test for `FailLevel`");
    }
}
*/
