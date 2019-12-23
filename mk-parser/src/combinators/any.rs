// Due to a bug in Clippy, warnings are produced from calling `impl_tup_any`
// below when there shouldn't be. We're disabling them here because it isn't
// currently possible to add attributes to macro expansions
#![allow(clippy::identity_op)]

// Most of the goings-on of this module are just macro expansions - there's no
// reason to expose that mess.
//
// That being said, there are a few items that are made public through
// `combinators`:
// * IntoAny
// * Either
// * any
// * DynAny
// As such, their documentation comments reflect that they are being used above
#![doc(hidden)]

use crate::{
    utils::{LazyString, Pos},
    source::Source,
    Parser, DynParser, ParseResult,
};

use std::ops::{BitOr, Add};

// TODO-DOC
pub fn any<P, A>(into_any: A) -> P
where
    P: Parser + sealed::Sealed,
    A: IntoAny<P>,
{
    into_any.into()
}

// TODO-DOC
pub trait IntoAny<P: Parser> {
    fn into(self) -> P;
}

pub mod sealed {
    pub trait Sealed {}
}

// TODO-DOC
pub struct Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
{
    pub(crate) left: P1,
    pub(crate) right: P2,
}

impl<P1, P2> sealed::Sealed for Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>
{}

impl<P1, P2> IntoAny<Either<P1, P2>> for (P1, P2)
where
    P1: Parser,
    P2: Parser<Output = P1::Output>
{
    fn into(self) -> Either<P1, P2> {
        Either {
            left: self.0,
            right: self.1,
        }
    }
}

impl<P1, P2> DynParser for Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
{
    type Output = P1::Output;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<P1::Output> {
        src.mark_backtrack();
        let pos = src.pos();

        let (l_pos, l_msg) = match self.left.parse(src, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o, _) => return ParseResult::Success(o, pos),
            ParseResult::Fail(p, 0, m) => (p, m),
            ParseResult::Fail(p, i, m) => {
                let msg = if let Some(m) = m {
                    Some(LazyString::new(move || {
                        format!(
                            "Higher-order fail encountered from left at {}:\n{}",
                            p,
                            String::from(m)
                        )
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!(
                            "{} {} {}",
                            "Higher-order fail encountered from left at", p, "without message"
                        )
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, i - 1, msg);
            }
        };

        src.backtrack();
        src.unmark_backtrack();

        let (r_pos, r_msg) = match self.right.parse(src, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o, _) => return ParseResult::Success(o, pos),
            ParseResult::Fail(p, 0, m) => (p, m),
            ParseResult::Fail(p, i, m) => {
                let msg = if let Some(m) = m {
                    Some(LazyString::new(move || {
                        format!(
                            "Higher-order fail encountered from right at {}:\n{}",
                            p,
                            String::from(m)
                        )
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!(
                            "{} {} {}",
                            "Higher-order fail encountered from right at", p, "without message"
                        )
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, i - 1, msg);
            }
        };

        if !msg_hint {
            ParseResult::Fail(pos, 0, None)
        } else {
            ParseResult::Fail(
                pos,
                0,
                Some(LazyString::new(move || {
                    let fmt = |msg: Option<LazyString>| {
                        msg.map(String::from)
                            .unwrap_or_else(|| String::from("no attached message"))
                    };

                    format!(
                        "Failed to match either parser:\n  * {}: {}\n  * {}: {}",
                        l_pos,
                        fmt(l_msg),
                        r_pos,
                        fmt(r_msg)
                    )
                })),
            )
        }
    }
}

impl<P1, P2> Parser for Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
{}

impl<P1, P2, P3> BitOr<P3> for Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
    P3: Parser<Output = P1::Output>,
{
    type Output = Any3<P1, P2, P3>;

    fn bitor(self, rhs: P3) -> Any3<P1, P2, P3> {
        Any3 {
            inner: (self.left, self.right, rhs)
        }
    }
}


impl<P1, P2, P3> Add<P3> for Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
    P3: Parser<Output = P1::Output>,
{
    impl_add!(P3);
}

macro_rules! special_impl_bitor {
    (
        Top:
        $any_head:ident, $any:ident @
        $p:ident, $($ps:ident),+ @
        $idx:tt @ $($idx_tail:tt)@+
    ) => {
        impl<P, $p, $($ps),+> BitOr<P> for $any<$p, $($ps),+>
        where
            $p: Parser,
            P: Parser<Output=$p::Output>,
            $($ps: Parser<Output=$p::Output>),+
        {
            impl_bitor!(P);
        }
    };

    (
        Middle:
        $any_head:ident, $any:ident @
        $p:ident, $($ps:ident),+ @
        $idx:tt @ $($idx_tail:tt)@+
    ) => {
        impl<P, $p, $($ps),+> BitOr<P> for $any<$p, $($ps),+>
        where
            $p: Parser,
            P: Parser<Output=$p::Output>,
            $($ps: Parser<Output=$p::Output>),+
        {
            type Output = $any_head<$p, $($ps),+, P>;

            fn bitor(self, rhs: P) -> Self::Output {
                let rev_tup = (self.inner.$idx, $(self.inner.$idx_tail),+);
                $any_head {
                    inner: (rev_tup.$idx, $(rev_tup.$idx_tail),+, rhs),
                }
            }
        }
    };
}

macro_rules! impl_tup_any {
    // We already have implementations for one and two - `Single` and `Either`,
    // so we don't need to recurse any further
    (
        $TOP:ident:
        $any:ident, $any_tail:ident @
        $p:ident, $ps:ident @
        $idx:tt @ $idx_tail:tt
    ) => {};

    (
        $TOP:ident:
        $any_head:ident, $any:ident, $($any_tail:ident),+ @
        $p:ident, $($ps:ident),+ @
        $idx:tt @ $($idx_tail:tt)@+
    ) => {
        pub struct $any<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser<Output=$p::Output>),+
        {
            // Note that these are in reverse order, going:
            // PN ... P2, P1
            inner: ($p, $($ps),+),
        }

        impl<$p, $($ps),+> sealed::Sealed for $any<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser<Output=$p::Output>),+
        {}

        impl<$p, $($ps),+> IntoAny<$any<$p, $($ps),+>> for ($p, $($ps),+)
        where
            $p: Parser,
            $($ps: Parser<Output=$p::Output>,)+
        {
            fn into(self) -> $any<$p, $($ps),+> {
                $any {
                    inner: self,
                }
            }
        }

        impl<$p, $($ps),+> DynParser for $any<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser<Output=$p::Output>,)+
        {
            type Output = $p::Output;

            fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Self::Output> {
                macro_rules! snd {
                    ( $x:ident, $y:expr ) => { $y }
                }

                let rev_psrs = (&self.inner.$idx, $(&self.inner.$idx_tail),+);

                // TODO: Because these are all the same type, they can actually
                // be changed to arrays
                let mut msgs = (snd!($p, None as Option<LazyString>),
                    $(snd!($ps, None as Option<LazyString>)),+);

                // These are just fillers; they will all be overwritten eventually
                let mut poss = (snd!($p, Pos { line: 0, col: 0 }),
                    $(snd!($ps, Pos { line: 0, col: 0 })),+);

                src.mark_backtrack();
                let pos = src.pos();

                {
                    let (p, m) = match rev_psrs.$idx.parse(src, msg_hint) {
                        ParseResult::Error(e) => return ParseResult::Error(e),
                        ParseResult::Success(o,_) => return ParseResult::Success(o, pos),
                        ParseResult::Fail(p,0,m) => (p, m),
                        ParseResult::Fail(p,i,m) => {
                            let msg = if let Some(m) = m {
                                Some(LazyString::new(move || {
                                    format!("{} #0 at {}:\n{}",
                                            "Higher-order fail encountered from `all` parser",
                                            p, String::from(m))
                                }))
                            } else if msg_hint {
                                Some(LazyString::new(move || {
                                    format!("{} #0 at {} without message",
                                            "Higher-order fail encountered from `all` parser",
                                            p)
                                }))
                            } else {
                                None
                            };

                            return ParseResult::Fail(pos, i-1, msg);
                        },
                    };
                    poss.$idx = p;
                    msgs.$idx = m;
                }

                $({
                    src.backtrack();

                    let (p, m) = match rev_psrs.$idx_tail.parse(src, msg_hint) {
                        ParseResult::Error(e) => return ParseResult::Error(e),
                        ParseResult::Success(o,_) => return ParseResult::Success(o, pos),
                        ParseResult::Fail(p,0,m) => (p, m),
                        ParseResult::Fail(p,i,m) => {
                            let msg = if let Some(m) = m {
                                Some(LazyString::new(move || {
                                    format!("{} #{:?} at {}:\n{}",
                                            "Higher-order fail encountered from `all` parser",
                                            $idx-$idx_tail, p, String::from(m))
                                }))
                            } else if msg_hint {
                                Some(LazyString::new(move || {
                                    format!("{} #{:?} at {} without message",
                                            "Higher-order fail encountered from `all` parser",
                                            $idx-$idx_tail, p)
                                }))
                            } else {
                                None
                            };

                            return ParseResult::Fail(pos, i-1, msg);
                        },
                    };
                    poss.$idx_tail = p;
                    msgs.$idx_tail = m;
                })+

                // This is an unfortuante missed optimization. Ideally, we'd
                // want this to be within the loop, but we can't isolate
                // everything but the last `$idx_tail` value.
                src.unmark_backtrack();

                if !msg_hint {
                    ParseResult::Fail(pos, 0, None)
                } else {
                    ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                        let fmt = |msg: Option<LazyString>| msg
                            .map(String::from)
                            .unwrap_or(String::from("no attached message"));

                        let mut s = format!("Failed to match `any` parser:\n  * {}: {}",
                                            poss.$idx, fmt(msgs.$idx));
                        $({
                            s.push_str(&format!("\n  * {}: {}",
                                           poss.$idx_tail, fmt(msgs.$idx_tail)));
                        })+

                        s
                    })))
                }
            }
        }

        impl<$p, $($ps),+> Parser for $any<$p, $($ps),+>
        where
            $p: Parser,
            $($ps: Parser<Output=$p::Output>,)+
        {}

        special_impl_bitor! {
            $TOP:
            $any_head, $any @
            $p, $($ps),+ @
            $idx @ $($idx_tail)@+
        }

        impl<P, $p, $($ps),+> Add<P> for $any<$p, $($ps),+>
        where
            $p: Parser,
            P: Parser<Output=$p::Output>,
            $($ps: Parser<Output=$p::Output>),+
        {
            impl_add!(P);
        }

        impl_tup_any! {
            Middle:
            $any, $($any_tail),+ @
            $($ps),+ @
            $($idx_tail)@+
        }
    };
}

impl_tup_any! {
    Top:

    Any_Padding,
    Any16, Any15, Any14, Any13, Any12, Any11, Any10, Any9, 
    Any8,  Any7,  Any6,  Any5,  Any4,  Any3,
    Any_Padding  @

    P15, P14, P13, P12, P11, P10, P9,  P8,
    P7,  P6,  P5,  P4,  P3,  P2,  P1,  P0 @

    15 @ 14 @ 13 @ 12 @ 11 @ 10 @ 9  @ 8  @
    7  @ 6  @ 5  @ 4  @ 3  @ 2  @ 1  @ 0
}

pub struct Single<P: Parser> {
    psr: P,
}

impl<P: Parser> sealed::Sealed for Single<P> {}

impl<P: Parser> IntoAny<Single<P>> for P {
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
// impl<P1: Parser, P2: Parser<Output = P1::Output>> BitOr<P2> for Single<P1> {
//     type Output = Either<P1, P2>;
// 
//     fn bitor(self, rhs: P2) -> Either<P1, P2> {
//         Either {
//             left: self.psr,
//             right: rhs,
//         }
//     }
// }

// // TODO: Is there any reason we'd need this?
// impl<P1: Parser, P2: Parser<Output = P1::Output>> Add<P2> for Single<P1> {
//     type Output = Chain<P1, P2>;
// 
//     fn add(self, rhs: P2) -> Chain<P1, P2> {
//         Chain {
//             first: self.psr,
//             second: rhs,
//         }
//     }
// }

// TODO-DOC
// TODO: Change this to a tuple struct with public field
pub struct DynAny<T> {
    inner: Vec<Box<dyn DynParser<Output = T>>>,
}

impl<T> DynAny<T> {
    // TODO-DOC
    pub fn new(v: Vec<Box<dyn DynParser<Output = T>>>) -> Self {
        DynAny { inner: v }
    }
}

impl<T> DynParser for DynAny<T> {
    type Output = T;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<T> {
        if self.inner.is_empty() {
            let msg = if msg_hint {
                Some(LazyString::new(|| {
                    String::from("`DynAny` has no parsers, cannot match")
                }))
            } else {
                None
            };

            return ParseResult::Fail(src.pos(), 0, msg);
        }

        if self.inner.len() != 1 {
            src.mark_backtrack();
        }

        let pos = src.pos();

        let mut poss: Vec<Pos> = Vec::with_capacity(self.inner.len());
        let mut msgs: Vec<Option<LazyString>> = Vec::with_capacity(self.inner.len());

        for (idx, psr) in self.inner.iter().enumerate() {
            if idx != 0 {
                // This only occurs if self.len() != 1
                src.backtrack();
            }

            if idx == self.inner.len() - 1 && self.inner.len() != 1 {
                src.unmark_backtrack();
            }

            let (p, m) = match psr.parse(src, msg_hint) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(t, _) => return ParseResult::Success(t, pos),
                ParseResult::Fail(p, 0, m) => (p, m),
                ParseResult::Fail(p, i, m) => {
                    let msg = if let Some(m) = m {
                        Some(LazyString::new(move || {
                            format!(
                                "{} #{} at {}:\n{}",
                                "Higher-order fail encountered from `DynAll` parser",
                                idx,
                                p,
                                String::from(m)
                            )
                        }))
                    } else if msg_hint {
                        Some(LazyString::new(move || {
                            format!(
                                "{} #{} at {} without message",
                                "Higher-order fail encountered from `DynAll` parser", idx, p
                            )
                        }))
                    } else {
                        None
                    };

                    return ParseResult::Fail(p, i - 1, msg);
                }
            };

            poss.push(p);
            msgs.push(m);
        }

        if !msg_hint {
            ParseResult::Fail(pos, 0, None)
        } else {
            ParseResult::Fail(
                pos,
                0,
                Some(LazyString::new(move || {
                    let fmt = |msg: Option<LazyString>| {
                        msg.map(String::from)
                            .unwrap_or_else(|| String::from("no attached message"))
                    };

                    let mut s = String::from("Failed to match `DynAny` parser:");

                    msgs.into_iter().map(fmt).zip(poss).for_each(|(m, p)| {
                        s.push_str(&format!("\n  * {}: {}", p, m));
                    });

                    s
                })),
            )
        }
    }
}

impl<T> Parser for DynAny<T> {}

impl<T, P: Parser<Output = T>> BitOr<P> for DynAny<T> {
    impl_bitor!(P);
}

impl<T, P: Parser<Output = T>> Add<P> for DynAny<T> {
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
    fn either() {
        // NOTE: This is a partial test. There's a lot more complicated failure
        // logic that isn't tested here.

        let s = "foobfoo...";
        let mut src = Source::new(s.as_bytes());

        let psr = StrLit("foo").or(StrLit("b"));
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "b");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
        assert!(psr.parse(&mut src, false).is_fail());
    }

    #[test]
    fn any() {
        // NOTE: This is a partial test. There's a lot more complicated failure
        // logic that isn't tested here.

        let s = "foobarbaz";
        let mut src = Source::new(s.as_bytes());

        let psr = StrLit("foo")
                | StrLit("bar")
                | StrLit("baz")
                | StrLit("foobar");

        /*
        let psr = super::any((
            StrLit("foo"),
            StrLit("bar"),
            StrLit("baz"),
            StrLit("foobar"),
        ));
        */

        assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "bar");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "baz");
        assert!(psr.parse(&mut src, false).is_fail());
    }

    #[test]
    fn dyn_any() {
        // NOTE: This is a partial test. There's a lot more complicated failure
        // logic that isn't tested here.
        // TODO

        let s = "foobarbaz";
        let mut src = Source::new(s.as_bytes());

        let psr = super::DynAny::new(vec![
            Box::new(StrLit("foo")),
            Box::new(StrLit("bar")),
            Box::new(StrLit("baz")),
            Box::new(StrLit("foobar")),
        ]);

        // println!("{:?}", psr.parse(&mut src, false).unwrap());
        // panic!("debug");

        assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "bar");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "baz");
        assert!(psr.parse(&mut src, false).is_fail());
    }
}
