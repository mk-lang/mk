use crate::{
    Parser,
    DynParser,
    ParseResult,
    utils::{LazyString, Pos},
    text::Source,
};

use std::{
    io::Read,
    marker::PhantomData,
};

// Section 1: "Normal" Combinators - those not requiring macros

pub struct Map<R, F, A, B, P>
where
    R: Read,
    F: 'static + Fn(A) -> B,
    P: Parser<R, Output=A>,
{
    psr: P,
    func: F,
    _marker: PhantomData<R>,
}

pub fn map<R, F, A, B, P>(psr: P, func: F) -> Map<R, F, A, B, P>
where
    R: Read,
    F: 'static + Fn(A) -> B,
    P: Parser<R, Output=A>,
{
    Map {
        psr,
        func,
        _marker: PhantomData,
    }
}

impl<R, F, A, B, P> DynParser<R> for Map<R, F, A, B, P>
where
    R: Read,
    F: 'static + Fn(A) -> B,
    P: Parser<R, Output=A>,
{
    type Output = B;
    
    fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<B> {
        match self.psr.parse(text, msg_hint) {
            ParseResult::Success(t, pos) => ParseResult::Success((self.func)(t), pos),
            ParseResult::Fail(pos, i, m) => ParseResult::Fail(pos, i, m),
            ParseResult::Error(e) => ParseResult::Error(e),
        }
    }
}

impl<R, F, A, B, P> Parser<R> for Map<R, F, A, B, P>
where
    R: Read,
    F: 'static + Fn(A) -> B,
    P: Parser<R, Output=A>,
{}

#[derive(Debug)]
pub struct Repeat<R, T, P>
where
    R: Read,
    P: Parser<R, Output=T>,
{
    lower: usize,
    upper: Option<usize>,
    psr: P,
    _marker: PhantomData<R>,
}

pub fn repeat<R, T, P>(psr: P, lower: usize, upper: Option<usize>) -> Repeat<R, T, P>
where
    R: Read,
    P: Parser<R, Output=T>,
{
    Repeat {
        lower,
        upper,
        psr,
        _marker: PhantomData,
    }
}

impl<R, T, P> DynParser<R> for Repeat<R, T, P>
where
    R: Read,
    P: Parser<R, Output=T>,
{
    type Output = Vec<T>;

    fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<Vec<T>> {
        // `pos` is used in various places throughout this function
        let pos = text.pos();

        // If the lower bound is greater than the upper bound, it's not
        // possible to parse. Additionally, the logic later requires this to
        // not be the case.
        if self.upper.is_some() && (self.lower > self.upper.unwrap()) {
            return match msg_hint {
                false => ParseResult::Fail(pos, 0, None),
                true => {
                    let (lower, upper) = (self.lower, self.upper);
                    ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                        format!("{} Lower bound {:?} > upper bound {:?}",
                                "Failed to match pattern repetition",
                                lower, upper.unwrap())
                    })))
                }
            };
        }

        let (mut ret, upper) = match self.upper {
            Some(u) => (Vec::with_capacity(u), u),
            None => (Vec::new(), std::usize::MAX),
        };

        for r in 0..self.lower {
            match self.psr.parse(text, msg_hint) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(o,_) => ret.push(o),
                ParseResult::Fail(p,i,m) => {
                    let msg = match msg_hint {
                        false => None,
                        true => match m {
                            Some(m) => {
                                let lower = self.lower;
                                Some(LazyString::new(move || {
                                    format!("{} {:?} {} {:?}. From {}:\n{}",
                                            "Only matched", r, "times, needed at least",
                                            lower, p, String::from(m))
                                }))
                            }
                            None => {
                                let lower = self.lower;
                                Some(LazyString::new(move || {
                                    format!("{} {:?} {} {:?} at {} {}.",
                                            "Only matched", r, "times, needed at least",
                                            lower, p, "without an additional message")
                                }))
                            },
                        },
                    };

                    let new_i = match i {
                        0 => 0,
                        _ => i - 1,
                    };

                    return ParseResult::Fail(pos, new_i, msg);
                },
            }
        }

        for r in self.lower..upper {
            text.mark_backtrack();

            match self.psr.parse(text, false) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(o,_) => ret.push(o),
                // If it's an expected error, we already have enough.
                ParseResult::Fail(_,0,_) => {
                    text.backtrack();
                    text.unmark_backtrack();
                    break
                },
                ParseResult::Fail(p,i,m) => {
                    text.backtrack();
                    text.unmark_backtrack();

                    // TODO: This can be simplified by re-ordering:
                    // e.g. `if m.is_some() { ... } else if msg_hint ...`
                    return if msg_hint && m.is_none() {
                        ParseResult::Fail(pos, i-1, Some(LazyString::new(move || {
                            format!("{} {:?} {} at {} {}.",
                                    "Matched", r, "times, higher-order fail encountered",
                                    p, "without message")
                        })))
                    } else if m.is_some() {
                        ParseResult::Fail(pos, i-1, Some(LazyString::new(move || {
                            format!("{} {:?} {}. From {}:\n{}",
                                    "Matched", r, "times, higher-order fail encountered",
                                    p, String::from(m.unwrap()))
                        })))
                    } else {
                        ParseResult::Fail(pos, i-1, None)
                    };
                },
            }

            text.unmark_backtrack();
        }

        ParseResult::Success(ret, pos)
    }
}

impl<R: Read, T, P: Parser<R, Output=T>> Parser<R> for Repeat<R, T, P> {}

pub struct Either<R, T, P1, P2>
where
    R: Read,
    P1: Parser<R, Output=T>,
    P2: Parser<R, Output=T>,
{
    left: P1,
    right: P2,
    _marker: PhantomData<R>,
}

pub fn either<R, T, P1, P2>(left: P1, right: P2) -> Either<R, T, P1, P2>
where
    R: Read,
    P1: Parser<R, Output=T>,
    P2: Parser<R, Output=T>,
{
    Either {
        left,
        right,
        _marker: PhantomData,
    }
}

impl<R, T, P1, P2> DynParser<R> for Either<R, T, P1, P2>
where
    R: Read,
    P1: Parser<R, Output=T>,
    P2: Parser<R, Output=T>,
{
    type Output = T;

    fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<T> {

        text.mark_backtrack();
        let pos = text.pos();

        let (l_pos, l_msg) = match self.left.parse(text, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o,_) => return ParseResult::Success(o, pos),
            ParseResult::Fail(p,0,m) => (p, m),
            ParseResult::Fail(p,i,m) => {
                let msg = if let Some(m) = m {
                    Some(LazyString::new(move || {
                        format!("Higher-order fail encountered from left at {}:\n{}",
                                p, String::from(m))
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!("{} {} {}",
                                "Higher-order fail encountered from left at", p,
                                "without message")
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, i-1, msg);
            },
        };

        text.backtrack();
        text.unmark_backtrack();

        let (r_pos, r_msg) = match self.right.parse(text, msg_hint) {
            ParseResult::Error(e) => return ParseResult::Error(e),
            ParseResult::Success(o,_) => return ParseResult::Success(o, pos),
            ParseResult::Fail(p,0,m) => (p, m),
            ParseResult::Fail(p,i,m) => {
                let msg = if let Some(m) = m {
                    Some(LazyString::new(move || {
                        format!("Higher-order fail encountered from right at {}:\n{}",
                                p, String::from(m))
                    }))
                } else if msg_hint {
                    Some(LazyString::new(move || {
                        format!("{} {} {}",
                                "Higher-order fail encountered from right at", p,
                                "without message")
                    }))
                } else {
                    None
                };

                return ParseResult::Fail(pos, i-1, msg);
            },
        };

        return match msg_hint {
            false => ParseResult::Fail(pos, 0, None),
            true => {
                return ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                    let fmt = |msg: Option<LazyString>| msg
                        .map(|l| String::from(l))
                        .unwrap_or(String::from("no attached message"));

                    format!("Failed to match either parser:\n  * {}: {}\n  * {}: {}",
                            l_pos, fmt(l_msg), r_pos, fmt(r_msg))
                })));
            },
        };
    }
}

impl<R, T, P1, P2> Parser<R> for Either<R, T, P1, P2>
where
    R: Read,
    P1: Parser<R, Output=T>,
    P2: Parser<R, Output=T>,
{}

// Section 2: Parsers with macros

// Section 2a: "Any"

pub fn any<R, T, P, A>(into_any: A) -> P
where
    R: Read,
    P: Parser<R, Output=T> + mod_any::sealed::Sealed,
    A: IntoAny<R, T, P>,
{
    into_any.into()
}

pub trait IntoAny<R, T, P>: mod_any::sealed::Sealed
where
    R: Read,
    P: Parser<R, Output=T> + mod_any::sealed::Sealed,
{
    fn into(self) -> P;
}

#[doc(hidden)]
pub mod mod_any {
    use super::*;

    pub(super) mod sealed {
        pub trait Sealed {}

        macro_rules! impl_tup {
            ( $t:ident ) => {
                impl<$t> Sealed for ($t,) {}
            };

            ( $t:ident, $($ts:ident),+ ) => {
                impl<$t, $($ts),+> Sealed for ($t, $($ts),+) {}

                impl_tup! {
                    $($ts),+
                }
            }
        }

        impl_tup! {
            T1,  T2,  T3,  T4,  T5,  T6,  T7,  T8,
            T9,  T10, T11, T12, T13, T14, T15, T16,
            T17, T18, T19, T20, T21, T22, T23, T24,
            T25, T26, T27, T28, T29, T30, T31, T32
        }
    }

    macro_rules! impl_tup_any {
        (
            $any:ident @
            $p:ident @
            $idx:tt
        ) => {
            pub struct $any<R, T, $p>
            where
                R: Read,
                $p: Parser<R, Output=T>,
            {
                // Just for ease of use, we're making this one not a tuple
                inner: $p,
                _marker: PhantomData<R>,
            }

            impl<R, T, $p> sealed::Sealed for $any<R, T, $p>
            where
                R: Read,
                $p: Parser<R, Output=T>,
            {}

            impl<R, T, $p> super::IntoAny<R, T, $any<R, T, $p>> for ($p,)
            where
                R: Read,
                $p: Parser<R, Output=T>,
            {
                fn into(self) -> $any<R, T, $p> {
                    $any {
                        inner: self.0,
                        _marker: PhantomData,
                    }
                }
            }

            impl<R, T, $p> DynParser<R> for $any<R, T, $p>
            where
                R: Read,
                $p: Parser<R, Output=T>,
            {
                type Output = T;

                fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<T> {
                    let pos = text.pos();

                    let (p, m) = match self.inner.parse(text, msg_hint) {
                        ParseResult::Error(e) => return ParseResult::Error(e),
                        ParseResult::Success(o,_) => return ParseResult::Success(o, pos),
                        ParseResult::Fail(p,0,m) => (p, m),
                        ParseResult::Fail(p,i,m) => {
                            let msg = if let Some(m) = m {
                                Some(LazyString::new(move || {
                                    format!("{} #0 at {}:\n{}",
                                            "Higher-order fail encountered from parser",
                                            p, String::from(m))
                                }))
                            } else if msg_hint {
                                Some(LazyString::new(move || {
                                    format!("{} #0 at {} without message",
                                            "Higher-order fail encountered from parser",
                                            p)
                                }))
                            } else {
                                None
                            };

                            return ParseResult::Fail(pos, i-1, msg);
                        },
                    };

                    return match msg_hint {
                        false => ParseResult::Fail(pos, 0, None),
                        true => {
                            return ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                                let fmt = |msg: Option<LazyString>| msg
                                    .map(|l| String::from(l))
                                    .unwrap_or(String::from("no attached message"));

                                format!("Failed to match `any` parser:\n  * {}: {}",
                                        p, fmt(m))
                            })));
                        },
                    };
                }
            }

            impl<R, T, $p> Parser<R> for $any<R, T, $p>
            where
                R: Read,
                $p: Parser<R, Output=T>,
            {}
        };

        (
            $any:ident, $($any_tail:ident),+ @
            $p:ident, $($ps:ident),+ @
            $idx:tt @ $($idx_tail:tt)@+
        ) => {
            pub struct $any<R, T, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=T>,
                $($ps: Parser<R, Output=T>),+
            {
                // Note that these are in reverse order, going:
                // PN ... P2, P1
                inner: ($p, $($ps),+),
                _marker: PhantomData<R>,
            }

            impl<R, T, $p, $($ps),+> sealed::Sealed for $any<R, T, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=T>,
                $($ps: Parser<R, Output=T>),+
            {}

            impl<R, T, $p, $($ps),+> super::IntoAny<R, T, $any<R, T, $p, $($ps),+>> for ($p, $($ps),+)
            where
                R: Read,
                $p: Parser<R, Output=T>,
                $($ps: Parser<R, Output=T>,)+
            {
                fn into(self) -> $any<R, T, $p, $($ps),+> {
                    $any {
                        inner: self,
                        _marker: PhantomData,
                    }
                }
            }

            impl<R, T, $p, $($ps),+> DynParser<R> for $any<R, T, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=T>,
                $($ps: Parser<R, Output=T>,)+
            {
                type Output = T;

                fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<T> {
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

                    text.mark_backtrack();
                    let pos = text.pos();

                    {
                        let (p, m) = match rev_psrs.$idx.parse(text, msg_hint) {
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
                        text.backtrack();

                        let (p, m) = match rev_psrs.$idx_tail.parse(text, msg_hint) {
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
                    text.unmark_backtrack();

                    return match msg_hint {
                        false => ParseResult::Fail(pos, 0, None),
                        true => {
                            ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                                let fmt = |msg: Option<LazyString>| msg
                                    .map(|l| String::from(l))
                                    .unwrap_or(String::from("no attached message"));

                                let mut s = format!("Failed to match `any` parser:\n  * {}: {}",
                                                    poss.$idx, fmt(msgs.$idx));
                                $({
                                    s.push_str(&format!("\n  * {}: {}",
                                                   poss.$idx_tail, fmt(msgs.$idx_tail)));
                                })+

                                s
                            })))
                        },
                    };
                }
            }

            impl<R, T, $p, $($ps),+> Parser<R> for $any<R, T, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=T>,
                $($ps: Parser<R, Output=T>,)+
            {}

            impl_tup_any! {
                $($any_tail),+ @
                $($ps),+ @
                $($idx_tail)@+
            }
        }
    }

    impl_tup_any! {
        Any15, Any14, Any13, Any12, Any11, Any10, Any9,  Any8,
        Any7,  Any6,  Any5,  Any4,  Any3,  Any2,  Any1,  Any0 @

        P15, P14, P13, P12, P11, P10, P9,  P8,
        P7,  P6,  P5,  P4,  P3,  P2,  P1,  P0 @

        15 @ 14 @ 13 @ 12 @ 11 @ 10 @ 9  @ 8  @
        7  @ 6  @ 5  @ 4  @ 3  @ 2  @ 1  @ 0
    }
}

// Section 2b: "All"

pub fn all<R, T, P, A>(into_all: A) -> P
where
    R: Read,
    P: Parser<R, Output=T> + mod_all::sealed::Sealed,
    A: IntoAll<R, T, P>,
{
    into_all.into()
}

pub trait IntoAll<R, T, P>: mod_all::sealed::Sealed
where
    R: Read,
    P: Parser<R, Output=T> + mod_all::sealed::Sealed,
{
    fn into(self) -> P;
}

#[doc(hidden)]
pub mod mod_all {
    use super::*;

    pub(super) mod sealed {
        pub trait Sealed {}

        macro_rules! impl_tup {
            ( $t:ident ) => {
                impl<$t> Sealed for ($t,) {}
            };

            ( $t:ident, $($ts:ident),+ ) => {
                impl<$t, $($ts),+> Sealed for ($t, $($ts),+) {}

                impl_tup! {
                    $($ts),+
                }
            }
        }

        impl_tup! {
            T1,  T2,  T3,  T4,  T5,  T6,  T7,  T8,
            T9,  T10, T11, T12, T13, T14, T15, T16,
            T17, T18, T19, T20, T21, T22, T23, T24,
            T25, T26, T27, T28, T29, T30, T31, T32
        }
    }

    macro_rules! impl_tup_all {
        (
            $all:ident @
            ($p:ident, $t:ident) @
            $oid:ident, $idx:tt
        ) => {
            pub struct $all<R, $t, $p>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
            {
                inner: $p,
                _marker: PhantomData<R>,
            }

            impl<R, $t, $p> sealed::Sealed for $all<R, $t, $p>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
            {}

            impl<R, $t, $p> super::IntoAll<R, $t, $all<R, $t, $p>> for ($p,)
            where
                R: Read,
                $p: Parser<R, Output=$t>,
            {
                fn into(self) -> $all<R, $t, $p> {
                    $all {
                        inner: self.0,
                        _marker: PhantomData,
                    }
                }
            }

            impl<R, $t, $p> DynParser<R> for $all<R, $t, $p>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
            {
                type Output = $t;

                fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<$t> {
                    let pos = text.pos();

                    let $oid = match self.inner.parse(text, msg_hint) {
                        ParseResult::Error(e) => return ParseResult::Error(e),
                        ParseResult::Success(o,_) => o,
                        ParseResult::Fail(p,i,m) => {
                            let msg = if m.is_some() && (i != 0 || msg_hint) {
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

                            let new_i = match i {
                                0 => 0,
                                _ => i-1,
                            };

                            return ParseResult::Fail(pos, new_i, msg);
                        },
                    };

                    return ParseResult::Success($oid, pos);
                }
            }

            impl<R, $t, $p> Parser<R> for $all<R, $t, $p>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
            {}
        };

        (
            $all:ident, $($all_tail:ident),+ @
            ($p:ident, $t:ident), $(($ps:ident, $ts:ident)),+ @
            $oid:ident, $idx:tt @ $($oids:ident, $idx_tail:tt)@+
        ) => {
            pub struct $all<R, $t, $($ts),+, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
                $($ps: Parser<R, Output=$ts>,)+
            {
                inner: ($p, $($ps),+),
                _marker: PhantomData<R>,
            }

            impl<R, $t, $($ts),+, $p, $($ps),+> sealed::Sealed for $all<R, $t, $($ts),+, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
                $($ps: Parser<R, Output=$ts>,)+
            {}

            impl<R, $t, $($ts),+, $p, $($ps),+> super::IntoAll<R, ($t,$($ts),+), $all<R, $t, $($ts),+, $p, $($ps),+>> for ($p,$($ps),+)
            where
                R: Read,
                $p: Parser<R, Output=$t>,
                $($ps: Parser<R, Output=$ts>,)+
            {
                fn into(self) -> $all<R, $t, $($ts),+, $p, $($ps),+> {
                    $all {
                        inner: self,
                        _marker: PhantomData,
                    }
                }
            }

            impl<R, $t, $($ts),+, $p, $($ps),+> DynParser<R> for $all<R, $t, $($ts),+, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
                $($ps: Parser<R, Output=$ts>,)+
            {
                type Output = ($t, $($ts),+);

                fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<($t, $($ts),+)> {
                    let pos = text.pos();

                    // reverse the parsers so that we can have everything in the
                    // right order
                    let rev_psrs = (&self.inner.$idx, $(&self.inner.$idx_tail),+);

                    let $oid = match rev_psrs.$idx.parse(text, msg_hint) {
                        ParseResult::Error(e) => return ParseResult::Error(e),
                        ParseResult::Success(o,_) => o,
                        ParseResult::Fail(p,i,m) => {
                            let msg = if m.is_some() && (i != 0 || msg_hint) {
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

                            let new_i = match i {
                                0 => 0,
                                _ => i-1,
                            };

                            return ParseResult::Fail(pos, new_i, msg);
                        },
                    };

                    $(let $oids = match rev_psrs.$idx_tail.parse(text, msg_hint) {
                        ParseResult::Error(e) => return ParseResult::Error(e),
                        ParseResult::Success(o,_) => o,
                        ParseResult::Fail(p,i,m) => {
                            let msg = if m.is_some() && (i != 0 || msg_hint) {
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

                            let new_i = match i {
                                0 => 0,
                                _ => i-1,
                            };

                            return ParseResult::Fail(pos, new_i, msg);
                        },
                    };)+

                    return ParseResult::Success(($oid, $($oids),+), pos);
                }
            }

            impl<R, $t, $($ts),+, $p, $($ps),+> Parser<R> for $all<R, $t, $($ts),+, $p, $($ps),+>
            where
                R: Read,
                $p: Parser<R, Output=$t>,
                $($ps: Parser<R, Output=$ts>,)+
            {}

            impl_tup_all! {
                $($all_tail),+ @
                $(($ps, $ts)),+ @
                $($oids, $idx_tail)@+
            }
        }
    }

    impl_tup_all! {
        All15, All14, All13, All12, All11, All10, All9,  All8,
        All7,  All6,  All5,  All4,  All3,  All2,  All1,  All0 @

        (P15, O15), (P14, O14), (P13, O13), (P12, O12),
        (P11, O11), (P10, O10), (P9,  O9 ), (P8,  O8 ),
        (P7,  O7 ), (P6,  O6 ), (P5,  O5 ), (P4,  O4 ),
        (P3,  O3 ), (P2,  O2 ), (P1,  O1 ), (P0,  O0 ) @

        o15, 15 @ o14, 14 @ o13, 13 @ o12, 12 @
        o11, 11 @ o10, 10 @ o9,  9  @ o8,  8  @
        o7,  7  @ o6,  6  @ o5,  5  @ o4,  4  @
        o3,  3  @ o2,  2  @ o1,  1  @ o0,  0
    }
}

// Section 3: dyn parsers

pub struct DynAny<R: Read, T> {
    inner: Vec<Box<dyn DynParser<R, Output=T>>>,
}

impl<R: Read, T> DynAny<R, T> {
    pub fn new(v: Vec<Box<dyn DynParser<R, Output=T>>>) -> Self {
        DynAny {
            inner: v,
        }
    }
}

impl<R: Read, T> DynParser<R> for DynAny<R, T> {
    type Output = T;

    fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<T> {
        if self.inner.len() == 0 {
            let msg = if msg_hint {
                Some(LazyString::new(|| {
                    String::from("`DynAny` has no parsers, cannot match")
                }))
            } else {
                None
            };

            return ParseResult::Fail(text.pos(), 0, msg);
        }

        if self.inner.len() != 1 {
            text.mark_backtrack();
        }

        let pos = text.pos();

        let mut poss: Vec<Pos> = Vec::with_capacity(self.inner.len());
        let mut msgs: Vec<Option<LazyString>> = Vec::with_capacity(self.inner.len());
        
        for (idx, psr) in self.inner.iter().enumerate() {
            if idx != 0 {
                // This only occurs if self.len() != 1
                text.backtrack();
            }

            if idx == self.inner.len() -1 && self.inner.len() != 1 {
                text.unmark_backtrack();
            }

            let (p, m) = match psr.parse(text, msg_hint) {
                ParseResult::Error(e) => return ParseResult::Error(e),
                ParseResult::Success(t,_) => return ParseResult::Success(t,pos),
                ParseResult::Fail(p,0,m) => (p, m),
                ParseResult::Fail(p,i,m) => {
                    let msg = if let Some(m) = m {
                        Some(LazyString::new(move || {
                            format!("{} #{} at {}:\n{}",
                                    "Higher-order fail encountered from `DynAll` parser",
                                    idx, p, String::from(m))
                        }))
                    } else if msg_hint {
                        Some(LazyString::new(move || {
                            format!("{} #{} at {} without message",
                                    "Higher-order fail encountered from `DynAll` parser",
                                    idx, p)
                        }))
                    } else {
                        None
                    };

                    return ParseResult::Fail(p, i-1, msg);
                }
            };

            poss.push(p);
            msgs.push(m);
        }

        return match msg_hint {
            false => ParseResult::Fail(pos, 0, None),
            true => {
                ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                    let fmt = |msg: Option<LazyString>| msg
                        .map(|lazy| String::from(lazy))
                        .unwrap_or(String::from("no attached message"));

                    let mut s = String::from("Failed to match `DynAny` parser:");

                    msgs.into_iter().map(fmt).zip(poss).for_each(|(m,p)| {
                        s.push_str(&format!("\n  * {}: {}", p, m));
                    });

                    s
                })))
            },
        };
    }
}

impl<R: Read, T> Parser<R> for DynAny<R, T> {}

#[cfg(test)]
mod tests {
    use crate::{
        DynParser,
        Parser,
        byte_lit,
        char_lit,
        string_lit,
        text::Source
    };

    #[test]
    fn map() {
        let s = "f";
        let mut src = Source::new(s.as_bytes());

        let psr = byte_lit(0x66).map(|c| format!("first! {}", c as char));
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "first! f");
    }

    #[test]
    fn repeat() {
        // NOTE: This is a partial test... There's a lot more complicated failure
        // logic within `repeat` that should be tested

        let s = "foofoo...BARBARBAR...";
        let mut src = Source::new(s.as_bytes());

        let foo = string_lit("foo").repeat(2, None);
        let dot = char_lit('.').repeat(0, Some(3));
        let bar = string_lit("BAR").repeat(0, None);

        assert_eq!(foo.parse(&mut src, false).unwrap().0, vec!["foo", "foo"]);
        assert_eq!(dot.parse(&mut src, false).unwrap().0, vec!['.', '.', '.']);
        assert_eq!(bar.parse(&mut src, false).unwrap().0, vec!["BAR", "BAR", "BAR"]);
    }

    #[test]
    fn either() {
        // NOTE: This is a partial test. There's a lot more complicated failure
        // logic that isn't tested here.

        let s = "foobfoo...";
        let mut src = Source::new(s.as_bytes());
        
        let psr = super::either(string_lit("foo"), string_lit("b"));
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

        let psr = super::any((
                string_lit("foo"),
                string_lit("bar"),
                string_lit("baz"),
                string_lit("foobar")));
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "bar");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "baz");
        assert!(psr.parse(&mut src, false).is_fail());
    }

    #[test]
    fn all() {
        // NOTE: This is a partial test - we need to adequately test failure as
        // well.

        let s = "foobarbaz";
        let mut src = Source::new(s.as_bytes());

        let psr = super::all((
                string_lit("foo"),
                string_lit("bar"),
                string_lit("baz")));
        assert_eq!(
            psr.parse(&mut src, false).unwrap().0,
            ("foo".into(), "bar".into(), "baz".into()));
    }

    #[test]
    fn dyn_any() {
        // NOTE: This is a partial test. There's a lot more complicated failure
        // logic that isn't tested here.

        let s = "foobarbaz";
        let mut src = Source::new(s.as_bytes());

        let psr = super::DynAny::new(vec![
                Box::new(string_lit("foo")),
                Box::new(string_lit("bar")),
                Box::new(string_lit("baz")),
                Box::new(string_lit("foobar"))]);

        // println!("{:?}", psr.parse(&mut src, false).unwrap());
        // panic!("debug");

        assert_eq!(psr.parse(&mut src, false).unwrap().0, "foo");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "bar");
        assert_eq!(psr.parse(&mut src, false).unwrap().0, "baz");
        assert!(psr.parse(&mut src, false).is_fail());
    }
}
