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
    source::Source,
    utils::{LazyString, Pos},
    DynParser, ParseResult, Parser,
};

#[cfg(feature = "bnf-syntax")]
use std::ops::{Add, BitOr};

/// Constructs a parser that matches when any of the given parsers match
///
/// [`IntoAny`] is implemented for n-tuples of parsers\* so that this function
/// can be called in a similar fashion to the example below:
///
/// \* `IntoAny` is only implemented on n-tuples up to n=16.
///
/// # Examples
///
/// ```
/// use mk_parser::{DynParser, Parser, source::Source};
/// use mk_parser::basics::{StrLit, char_lit};
/// use mk_parser::combinators::any;
///
/// let s = "foo☺bar";
/// let mut src = Source::new(s.as_bytes());
///
/// // Note that this trivial example is intentionally convoluted in order to
/// // demonstrate the flexibility of types allowed here.
/// let psr = any((StrLit("foo"), char_lit('☺').map(|_| "☺"), StrLit("bar")));
///
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "☺");
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "bar");
/// ```
///
/// [`IntoAny`]: trait.IntoAny.html
pub fn any<A: IntoAny>(into_any: A) -> A::Output {
    into_any.into()
}

/// A trait that is implemented on n-tuples of parsers, up to n=16
///
/// This is essentially a clone of [`IntoAll`].
///
/// Information about its usage can be found in the function [`any`]. The rest
/// of the writing here is meant for people who like to abuse the crates they
/// import.
///
/// It may be useful to know that `IntoAny` isn't implemented on singleton
/// tuples (of the form `(P,)`) - it is instead implement for the types itself,
/// thus it is implemented on every parser as well. Calling [`any`] with a
/// single parser (which might be necessary if you're designing macros
/// yourself) could be done like:
/// ```no_run
/// # use mk_parser::{combinators::any, basics::StrLit};
/// # let _ = {
/// any(StrLit("foo"))
/// # };
/// ```
/// These details are thankfully likely not relevant to "typical" users of this
/// crate.
///
/// [`IntoAll`]: trait.IntoAll.html
/// [`any`]: fn.any.html
pub trait IntoAny: sealed::Sealed {
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

/// Parser combinator that matches on either one parser or the other
///
/// This parser is typically constructed with the parser method [`Parser::or`],
/// but is also the resulting parser from calling [`any`] with two inputs.
///
/// Both of the parsers must have the same output type.
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
/// let psr = StrLit("foo").or(StrLit("-bar"));
///
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "-bar");
/// ```
///
/// For matching any one of a larger set of parsers, it is recommended to use
/// [`any`] - or [`DynAny`] if that set is not known at compile-time.
///
/// [`Parser::or`]: trait.Parser.html#method.or
/// [`any`]: fn.any.html
/// [`DynAny`]: struct.DynAny.html
pub struct Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
{
    pub(crate) left: P1,
    pub(crate) right: P2,
}

impl<P1, P2> IntoAny for (P1, P2)
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
{
    type Output = Either<P1, P2>;

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
{
}

#[cfg(feature = "bnf-syntax")]
impl<P1, P2, P3> BitOr<P3> for Either<P1, P2>
where
    P1: Parser,
    P2: Parser<Output = P1::Output>,
    P3: Parser<Output = P1::Output>,
{
    type Output = Any3<P1, P2, P3>;

    fn bitor(self, rhs: P3) -> Any3<P1, P2, P3> {
        Any3 {
            inner: (self.left, self.right, rhs),
        }
    }
}

#[cfg(feature = "bnf-syntax")]
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
        #[cfg(feature = "bnf-syntax")]
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
        #[cfg(feature = "bnf-syntax")]
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
    // We already have implementations for one and two, so we don't need to
    // recurse any further
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

        impl<$p, $($ps),+> IntoAny for ($p, $($ps),+)
        where
            $p: Parser,
            $($ps: Parser<Output=$p::Output>,)+
        {
            type Output = $any<$p, $($ps),+>;

            fn into(self) -> Self::Output {
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

        #[cfg(feature = "bnf-syntax")]
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

impl<P: Parser> IntoAny for P {
    type Output = Self;

    fn into(self) -> Self {
        self
    }
}

/// Parser that matches any of a runtime list of parsers
///
/// Unlike the function [`any`], this parser allows the computation of the
/// sequence of parsers to be deferred until runtime. It *will* be slower than
/// anything computed at compile-time, so this type should be used exclusively
/// for cases where it cannot be avoided. For other scenarios, see [`any`].
///
/// [`any`]: fn.any.html
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
///     combinators::DynAny,
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
/// let psr = DynAny(vec![gen_psr(0), gen_psr(1), gen_psr(2)]);
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "zero");
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, " ");
/// assert_eq!(psr.parse(&mut src, false).unwrap().0, "two");
/// ```
///
/// [`any`]: fn.any.html
pub struct DynAny<T>(pub Vec<Box<dyn DynParser<Output = T>>>);

impl<T> DynParser for DynAny<T> {
    type Output = T;

    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<T> {
        if self.0.is_empty() {
            let msg = if msg_hint {
                Some(LazyString::new(|| {
                    String::from("`DynAny` has no parsers, cannot match")
                }))
            } else {
                None
            };

            return ParseResult::Fail(src.pos(), 0, msg);
        }

        // We could choose to not mark if len == 1, but this is simpler and the
        // cost of marking is effectively zero.
        src.mark_backtrack();
        let mut is_marked = true;

        let pos = src.pos();

        let mut poss: Vec<Pos> = Vec::with_capacity(self.0.len());
        let mut msgs: Vec<Option<LazyString>> = Vec::with_capacity(self.0.len());

        for (idx, psr) in self.0.iter().enumerate() {
            // We could check if idx == 0 instead, but this is more clear
            if is_marked {
                src.backtrack();
            }

            // Minor optimization: Don't store for backtracking on the last
            // iteration of the loop.
            if idx == self.0.len() - 1 && is_marked {
                src.unmark_backtrack();
                is_marked = false;
            }

            let (p, m) = match psr.parse(src, msg_hint) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(t, _) => {
                    if is_marked {
                        src.unmark_backtrack();
                    }

                    return ParseResult::Success(t, pos)
                },
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

                    if is_marked {
                        src.unmark_backtrack()
                    }

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

#[cfg(feature = "bnf-syntax")]
impl<T, P: Parser<Output = T>> BitOr<P> for DynAny<T> {
    impl_bitor!(P);
}

#[cfg(feature = "bnf-syntax")]
impl<T, P: Parser<Output = T>> Add<P> for DynAny<T> {
    impl_add!(P);
}

#[cfg(test)]
mod tests {
    use crate::{basics::StrLit, source::Source, DynParser, Parser};

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

        // let psr = StrLit("foo") | StrLit("bar") | StrLit("baz") | StrLit("foobar");

        let psr = super::any((
            StrLit("foo"),
            StrLit("bar"),
            StrLit("baz"),
            StrLit("foobar"),
        ));

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

        let psr = super::DynAny(vec![
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
