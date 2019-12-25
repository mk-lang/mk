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

use crate::{source::Source, utils::LazyString, DynParser, ParseResult, Parser};

#[cfg(feature = "bnf-syntax")]
use std::ops::{Add, BitOr};

/// Constructs a parser that matches only when each given parser matches in
/// succession.
///
/// [`IntoAll`] is implemented for n-tuples of parsers\* so that this function
/// can be called in a similar fashion to the example below:
///
/// \* `IntoAll` is only implemented on n-tuples up to n=16.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, Parser, source::Source};
/// use mk_parser::basics::{StrLit, char_lit};
/// use mk_parser::combinators::all;
///
/// let s = "foo☺bar";
/// let mut src = Source::new(s.as_bytes());
///
/// // Note that this trivial example is intentionally convoluted in order to
/// // demonstrate the flexibility of types allowed here.
/// let psr = all((StrLit("foo"), char_lit('☺').map(|_| "☺"), StrLit("bar")));
///
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, ("foo", "☺", "bar"));
/// ```
///
/// [`IntoAll`]: trait.IntoAll.html
pub fn all<A: IntoAll>(into_all: A) -> A::Output {
    into_all.into()
}

/// A trait that is implemented on n-tuples of parsers, up to n=16
///
/// This is essentially a clone of [`IntoAny`].
///
/// Information about its usage can be found in the function [`all`]. The rest
/// of the writing here is meant for people who like to abuse the crates they
/// import.
///
/// It may be useful to know that `IntoAll` isn't implemented on singleton
/// tuples (of the form `(P,)`) - it is instead implement for the types itself,
/// thus it is implemented on every parser as well. Calling [`all`] with a
/// single parser (which might be necessary if you're designing macros
/// yourself) could be done like:
/// ```no_run
/// # use mk_parser::{combinators::all, basics::StrLit};
/// # let _ = {
/// all(StrLit("foo"))
/// # };
/// ```
/// These details are thankfully likely not relevant to "typical" users of this
/// crate.
///
/// [`IntoAny`]: trait.IntoAny.html
/// [`all`]: fn.all.html
pub trait IntoAll: sealed::Sealed {
    type Output: Parser;

    fn into(self) -> Self::Output;
}

pub mod sealed {
    pub trait Sealed {}

    macro_rules! impl_sealed {
        ( $p:ident, $($ps:ident),+ ) => {
            impl<$p, $($ps),+> Sealed for ($p, $($ps),+)
            where
                $p: $crate::Parser,
                $($ps: $crate::Parser),+
            {}

            impl_sealed!( $($ps),+ );
        };

        ( $p:ident ) => {
            impl<P: $crate::Parser> Sealed for P {}
        }
    }

    impl_sealed! {
        P16, P15, P14, P13, P12, P11, P10, P9,
        P8,  P7,  P6,  P5,  P4,  P3,  P2,  P1
    }
}

/// Parser combinator that matches on one parser followed by another
///
/// This parser is typically constructed with the parser method [`Parser::and`],
/// but is also the resulting parser from calling [`all`] with two inputs.
///
/// The output type of this parser is a tuple where the first element is the
/// output from the first parser's match and the second is the output from the
/// second.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, Parser, source::Source};
/// use mk_parser::basics::StrLit;
///
/// let s = "foo-bar";
/// let mut src = Source::new(s.as_bytes());
///
/// let psr = StrLit("foo").and(StrLit("-bar"));
///
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, ("foo", "-bar"));
/// ```
///
/// For matching many parsers in sequence, it is recommended to use [`all`] -
/// or [`DynAll`] if that sequence is not known at compile-time.
///
/// [`Parser::and`]: trait.Parser.html#method.and
/// [`all`]: fn.all.html
/// [`DynAll`]: struct.DynAll.html
pub struct Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
{
    pub(crate) first: P1,
    pub(crate) second: P2,
}

impl<P1: Parser, P2: Parser> IntoAll for (P1, P2) {
    type Output = Chain<P1, P2>;

    fn into(self) -> Chain<P1, P2> {
        Chain {
            first: self.0,
            second: self.1,
        }
    }
}

impl<P1: Parser, P2: Parser> DynParser for Chain<P1, P2> {
    type Output = (P1::Output, P2::Output);

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Self::Output> {
        let pos = src.pos();

        let first = match self.first.parse(src, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o, _) => o,
            ParseResult::Fail(p, lvl, m) => {
                let msg = if m.is_some() && (lvl != 0 || msg_hint) {
                    Some(LazyString::new(move || {
                        format!(
                            "{} at {}:\n{}",
                            "Failed to match first parser",
                            p,
                            String::from(m.unwrap())
                        )
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!(
                            "{} at {} without message",
                            "Failed to match first parser", p
                        )
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, lvl, msg);
            }
        };

        let second = match self.second.parse(src, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o, _) => o,
            ParseResult::Fail(p, lvl, m) => {
                let msg = if m.is_some() && (lvl != 0 || msg_hint) {
                    Some(LazyString::new(move || {
                        format!(
                            "{} at {}:\n{}",
                            "Failed to match second parser",
                            p,
                            String::from(m.unwrap())
                        )
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!(
                            "{} at {} without message",
                            "Failed to match second parser", p
                        )
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, lvl, msg);
            }
        };

        ParseResult::Success((first, second), pos)
    }
}

impl<P1, P2> Parser for Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
{
}

#[cfg(feature = "bnf-syntax")]
impl<P1, P2, P3> BitOr<P3> for Chain<P1, P2>
where
    P1: Parser,
    P2: Parser,
    P3: Parser<Output = (P1::Output, P2::Output)>,
{
    impl_bitor!(P3);
}

#[cfg(feature = "bnf-syntax")]
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
        // We don't want to implement it for the highest number, because that
        // could lead to obscure errors if someone (for **SOME** reason) were
        // to try to chain more than 16 parsers together.
    };

    (
        Middle:
        $all_head:ident, $all:ident, $($all_tail:ident),+ @
        $p:ident, $($ps:ident),+ @
        $oid:ident, $idx:tt @ $($oids:ident, $idx_tail:tt)@+
    ) => {
        #[cfg(feature = "bnf-syntax")]
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
        pub struct $all<$p: Parser, $($ps: Parser),+> {
            inner: ($p, $($ps),+),
        }

        impl<$p: Parser, $($ps: Parser),+> IntoAll for ($p,$($ps),+) {
            type Output = $all<$p, $($ps),+>;

            fn into(self) -> Self::Output {
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

        #[cfg(feature = "bnf-syntax")]
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

impl<P: Parser> IntoAll for P {
    type Output = Self;

    fn into(self) -> Self {
        self
    }
}

/// Parser that matches when an entire runtime sequence of parsers matches
///
/// Unlike the function [`all`], this parser allows the calculation of the
/// sequence of parsers to be deferred until runtime. It *will* be slower than
/// one computed at compile-time, so this type should be used exclusively for
/// cases where the combinator **must** be built at runtime. For other uses,
/// see [`all`].
///
/// # Examples
///
/// For this case, the types can't be computed at compile-time. If you need to,
/// it should be simple enough to extend this idea to cases where the length of
/// the sequence isn't known at compile-time either.
/// ```
/// use mk_parser::{
///     Parser, DynParser,
///     source::Source,
///     basics::{StrLit, char_lit, StringLit},
///     combinators::DynAll,
/// };
///
/// fn gen_psr(i: i32) -> Box<dyn DynParser<Output = String>> {
///     match i {
///         0 => Box::new(StrLit("zero").map(String::from)),
///         1 => Box::new(char_lit(' ').map(|_| String::from(" "))),
///         _ => Box::new(StringLit(String::from("two")).name("Special number two!")),
///     }
/// }
///
/// let s = "zero two";
/// let mut src = Source::new(s.as_bytes());
///
/// let psr = DynAll(vec![gen_psr(0), gen_psr(1), gen_psr(2)]);
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, &["zero", " ", "two"]);
/// ```
///
/// [`all`]: fn.all.html
pub struct DynAll<T>(pub Vec<Box<dyn DynParser<Output = T>>>);

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
                            format!(
                                "{} #{} at {}:\n{}",
                                "Failed to match dyn parser",
                                i,
                                p,
                                String::from(m.unwrap())
                            )
                        }))
                    } else if msg_hint {
                        Some(LazyString::new(move || {
                            format!(
                                "{} #{} at {} without message",
                                "Failed to match dyn parser", i, p
                            )
                        }))
                    } else {
                        None
                    };

                    return ParseResult::Fail(pos, lvl, msg);
                }
            };

            outs.push(t);
        }

        ParseResult::Success(outs, pos)
    }
}

impl<T> Parser for DynAll<T> {}

#[cfg(feature = "bnf-syntax")]
impl<T, P: Parser<Output = Vec<T>>> BitOr<P> for DynAll<T> {
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<T, P: Parser<Output = Vec<T>>> Add<P> for DynAll<T> {
    impl_add!(P);
}

#[cfg(test)]
mod tests {
    use crate::{basics::StrLit, source::Source, DynParser, Parser};

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

        // The first couple few are simply checking that it compiles properly
        let _psr = super::all(StrLit("foo"));
        let _psr = super::all((StrLit("foo"), StrLit("bar")));
        let psr = super::all((StrLit("foo"), StrLit("bar"), StrLit("baz")));
        // let psr = StrLit("foo") + StrLit("bar") + StrLit("baz");
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
            Box::new(StrLit("-baz")),
        ]);

        assert_eq!(
            psr.parse(&mut src, false).unwrap().0,
            ["foo", "-bar", "-baz"]
        );
    }
}
