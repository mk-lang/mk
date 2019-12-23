// Due to a bug in Clippy, warnings are produced from calling `impl_tup_any`
// below when there shouldn't be. We're disabling them here because it isn't
// currently possible to add attributes to macro expansions
#![allow(clippy::identity_op)]

// Most of the goings-on of this module are just macro expansions - there's no
// reason to expose that mess.
//
// That being said, there are a few items that are made public through
// `combinators`:
// * IntoAll
// * Chain
// * all
// * DynAll
// As such, their documentation comments reflect that they are being used above
#![doc(hidden)]

use crate::{
    utils::LazyString,
    source::Source,
    Parser, DynParser, ParseResult,
};

use std::ops::{BitOr, Add};

// TODO-DOC
pub fn all<P, A>(into_all: A) -> P
where
    P: Parser + sealed::Sealed,
    A: IntoAll<P>,
{
    into_all.into()
}

// TODO-DOC
pub trait IntoAll<P>
where
    P: Parser + sealed::Sealed,
{
    fn into(self) -> P;
}

pub(super) mod sealed {
    pub trait Sealed {}
}

// TODO-DOC
pub struct Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
{
    pub(crate) first: P1,
    pub(crate) second: P2,
}

impl<P1, P2> sealed::Sealed for Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
{}

impl<P1, P2> IntoAll<Chain<P1, P2>> for (P1, P2)
where
    P1: Parser,
    P2: Parser,
{
    fn into(self) -> Chain<P1, P2> {
        Chain {
            first: self.0,
            second: self.1,
        }
    }
}

impl<P1, P2> DynParser for Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
{
    type Output = (P1::Output, P2::Output);
    
    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Self::Output> {
        let pos = src.pos();

        let first = match self.first.parse(src, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o,_) => o,
            ParseResult::Fail(p,lvl,m) => {
                let msg = if m.is_some() && (lvl != 0 || msg_hint) {
                    Some(LazyString::new(move || {
                        format!("{} at {}:\n{}",
                                "Failed to match first parser",
                                p, String::from(m.unwrap()))
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!("{} at {} without message",
                                "Failed to match first parser",
                                p)
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, lvl, msg);
            },
        };

        let second = match self.second.parse(src, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o,_) => o,
            ParseResult::Fail(p,lvl,m) => {
                let msg = if m.is_some() && (lvl != 0 || msg_hint) {
                    Some(LazyString::new(move || {
                        format!("{} at {}:\n{}",
                                "Failed to match second parser",
                                p, String::from(m.unwrap()))
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!("{} at {} without message",
                                "Failed to match second parser",
                                p)
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, lvl, msg);
            },
        };

        ParseResult::Success((first, second), pos)
    }
}

impl<P1, P2> Parser for Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
{}

impl<P1, P2, P3> BitOr<P3> for Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
    P3: Parser<Output = (P1::Output, P2::Output)>,
{
    impl_bitor!(P3);
}

impl<P1, P2, P3> Add<P3> for Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
    P3: Parser,
{
    type Output = All3<P1, P2, P3>;

    fn add(self, rhs: P3) -> All3<P1, P2, P3> {
        All3 {
            inner: (self.first, self.second, rhs),
        }
    }
}

macro_rules! special_impl_add {
    (
        Top:
        $all_head:ident, $all:ident, $($all_tail:ident),+ @
        $p:ident, $($ps:ident),+ @
        $oid:ident, $idx:tt @ $($oids:ident, $idx_tail:tt)@+
    ) => {
        impl<P, $p, $($ps),+> Add<P> for $all<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser,)+
            P: Parser<Output = <Self as DynParser>::Output>,
        {
            impl_add!(P);
        }
    };

    (
        Middle:
        $all_head:ident, $all:ident, $($all_tail:ident),+ @
        $p:ident, $($ps:ident),+ @
        $oid:ident, $idx:tt @ $($oids:ident, $idx_tail:tt)@+
    ) => {
        impl<P, $p, $($ps),+> Add<P> for $all<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser,)+
            P: Parser<Output = <Self as DynParser>::Output>,
        {
            type Output = $all_head<$p, $($ps),+, P>;

            fn add(self, rhs: P) -> Self::Output {
                let rev_tup = (self.inner.$idx, $(self.inner.$idx_tail),+);
                $all_head {
                    inner: (rev_tup.$idx, $(rev_tup.$idx_tail),+, rhs),
                }
            }
        }
    };
}

macro_rules! impl_tup_all {
    (
        $TOP:ident:
        $all_head:ident, $all:ident, $all_tail:ident @
        $p:ident, $ps:ident @
        $oid:ident, $idx:tt @ $oids:ident, $idx_tail:tt
    ) => {};

    (
        $TOP:ident:
        $all_head:ident, $all:ident, $($all_tail:ident),+ @
        $p:ident, $($ps:ident),+ @
        $oid:ident, $idx:tt @ $($oids:ident, $idx_tail:tt)@+
    ) => {
        pub struct $all<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser),+
        {
            inner: ($p, $($ps),+),
        }

        impl<$p, $($ps),+> sealed::Sealed for $all<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser),+
        {}

        impl<$p, $($ps),+> IntoAll<$all<$p, $($ps),+>> for ($p,$($ps),+)
        where
            $p: Parser,
            $($ps: Parser),+
        {
            fn into(self) -> $all<$p, $($ps),+> {
                $all {
                    inner: self,
                }
            }
        }

        impl<$p, $($ps),+> DynParser for $all<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser),+
        {
            type Output = ($p::Output, $($ps::Output),+);

            fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Self::Output> {
                let pos = src.pos();

                // reverse the parsers so that we can have everything in the
                // right order
                let rev_psrs = (&self.inner.$idx, $(&self.inner.$idx_tail),+);

                let $oid = match rev_psrs.$idx.parse(src, msg_hint) {
                    ParseResult::Error(e) => return ParseResult::Error(e),
                    ParseResult::Success(o,_) => o,
                    ParseResult::Fail(p,lvl,m) => {
                        let msg = if m.is_some() && (lvl != 0 || msg_hint) {
                            Some(LazyString::new(move || {
                                format!("{} #0 at {}:\n{}",
                                        "Failed to match parser",
                                        p, String::from(m.unwrap()))
                            }))
                        } else if msg_hint {
                            Some(LazyString::new(move || {
                                format!("{} #0 at {} without message",
                                        "Failed to match parser", p)
                            }))
                        } else {
                            None
                        };

                        return ParseResult::Fail(pos, lvl, msg);
                    },
                };

                $(let $oids = match rev_psrs.$idx_tail.parse(src, msg_hint) {
                    ParseResult::Error(e) => return ParseResult::Error(e),
                    ParseResult::Success(o,_) => o,
                    ParseResult::Fail(p,lvl,m) => {
                        let msg = if m.is_some() && (lvl != 0 || msg_hint) {
                            Some(LazyString::new(move || {
                                format!("{} #{:?} at {}:\n{}",
                                        "Failed to match parser",
                                        p, $idx-$idx_tail, String::from(m.unwrap()))
                            }))
                        } else if msg_hint {
                            Some(LazyString::new(move || {
                                format!("{} #{:?} at {} without message",
                                        "Failed to match parser",
                                        $idx-$idx_tail, p)
                            }))
                        } else {
                            None
                        };

                        return ParseResult::Fail(pos, lvl, msg);
                    },
                };)+

                return ParseResult::Success(($oid, $($oids),+), pos);
            }
        }

        impl<$p, $($ps),+> Parser for $all<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser),+
        {}

        impl<P, $p, $($ps),+> BitOr<P> for $all<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser,)+
            P: Parser<Output = <Self as DynParser>::Output>,
        {
            impl_bitor!(P);
        }

        special_impl_add! {
            $TOP:
            $all_head, $all, $($all_tail),+ @
            $p, $($ps),+ @
            $oid, $idx @ $($oids, $idx_tail)@+
        }

        impl_tup_all! {
            Middle:
            $all, $($all_tail),+ @
            $($ps),+ @
            $($oids, $idx_tail)@+
        }
    };
}

impl_tup_all! {
    Top:

    All_Pad,
    All16, All15, All14, All13, All12, All11, All10, All9,
    All8,  All7,  All6,  All5,  All4,  All3,  All2,  All1 @

    P15, P14, P13, P12,
    P11, P10, P9,  P8,
    P7,  P6,  P5,  P4,
    P3,  P2,  P1,  P0 @

    o15, 15 @ o14, 14 @ o13, 13 @ o12, 12 @
    o11, 11 @ o10, 10 @ o9,  9  @ o8,  8  @
    o7,  7  @ o6,  6  @ o5,  5  @ o4,  4  @
    o3,  3  @ o2,  2  @ o1,  1  @ o0,  0
}

pub struct Single<P: Parser> {
    psr: P,
}

impl<P: Parser> sealed::Sealed for Single<P> {}

impl<P: Parser> IntoAll<Single<P>> for P {
    fn into(self) -> Single<P> {
        Single {
            psr: self,
        }
    }
}

impl<P: Parser> DynParser for Single<P> {
    type Output = P::Output;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<P::Output> {
        self.psr.parse(src, msg_hint)
    }
}

impl<P: Parser> Parser for Single<P> {}


// // TODO: Is there any reason we'd need this?
// impl<P: Parser, P2: Parser<Output = P::Output>> BitOr<P2> for Single<P> {
//     impl_bitor!(P2);
// }

// TODO-DOC
pub struct DynAll<T>(pub Vec<Box<dyn DynParser<Output=T>>>);

impl<T> DynParser for DynAll<T> {
    type Output = Vec<T>;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Vec<T>> {
        let pos = src.pos();
        let mut outs = Vec::with_capacity(self.0.len());

        for (i, psr) in self.0.iter().enumerate() {
            let t = match psr.parse(src, msg_hint) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(t, _) => t,
                ParseResult::Fail(p, lvl, m) => {
                    let msg = if m.is_some() && (lvl != 0 || msg_hint) {
                        Some(LazyString::new(move || {
                            format!("{} #{} at {}:\n{}",
                                    "Failed to match dyn parser",
                                    i, p, String::from(m.unwrap()))
                        }))
                    } else if msg_hint {
                        Some(LazyString::new(move || {
                            format!("{} #{} at {} without message",
                                    "Failed to match dyn parser",
                                    i, p)
                        }))
                    } else {
                        None
                    };

                    return ParseResult::Fail(pos, lvl, msg);
                },
            };

            outs.push(t);
        }

        ParseResult::Success(outs, pos)
    }
}

impl<T> Parser for DynAll<T> {}

impl<T, P: Parser<Output = Vec<T>>> BitOr<P> for DynAll<T> {
    impl_bitor!(P);
}

impl<T, P: Parser<Output = Vec<T>>> Add<P> for DynAll<T> {
    impl_add!(P);
}

#[cfg(test)]
mod tests {
    use crate::{
        basics::StrLit,
        source::Source,
        DynParser, Parser,
    };

    #[test]
    fn chain() {
        // TODO: More comprehensive test
        let s = "foobarbazfoobar";
        let mut src = Source::new(s.as_bytes());

        let psr = StrLit("foo").and(StrLit("bar"));
        assert_eq!(psr.parse(&mut src, false).unwrap().0, ("foo", "bar"));
        assert!(psr.parse(&mut src, false).is_fail());
        assert!(psr.parse(&mut src, false).is_success());
    }

    #[test]
    fn all() {
        // NOTE: This is a partial test - we need to adequately test failure as
        // well.
        // TODO

        let s = "foobarbaz";
        let mut src = Source::new(s.as_bytes());

        let _psr = super::all((StrLit("foo"), StrLit("bar")));
        let _psr = super::all((StrLit("foo"), StrLit("bar"), StrLit("baz")));
        let psr = StrLit("foo") + StrLit("bar") + StrLit("baz");
        assert_eq!(
            psr.parse(&mut src, false).unwrap().0,
            ("foo".into(), "bar".into(), "baz".into())
        );
    }

    #[test]
    fn dyn_all() {
        // TODO: More comprehensive test

        let s = "foo-bar-baz";
        let mut src = Source::new(s.as_bytes());

        let psr = super::DynAll(vec![
                                Box::new(StrLit("foo")),
                                Box::new(StrLit("-bar")),
                                Box::new(StrLit("-baz"))]);
        
        assert_eq!(psr.parse(&mut src, false).unwrap().0, ["foo", "-bar", "-baz"]);
    }
}
