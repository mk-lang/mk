use crate::{text::Source, ParseResult, Parser, LazyString, Pos};

use std::io::Read;
use std::marker::PhantomData;

// Section 1: "Normal" Combinators - those not requiring macros

pub struct Map<'a, F, A, B, P, R>
where
    F: 'a + Clone + Fn(A) -> B,
    P: Parser<'a, R, Output = A>,
    R: Read,
{
    psr: P,
    func: F,
    _marker: PhantomData<&'a (A, B, R)>,
}

impl<'a, F, A, B, P, R> Clone for Map<'a, F, A, B, P, R>
where
    F: 'a + Clone + Fn(A) -> B,
    P: Parser<'a, R, Output = A>,
    R: Read,
{
    fn clone(&self) -> Self {
        Map {
            psr: self.psr.clone(),
            func: self.func.clone(),
            _marker: PhantomData,
        }
    }
}

pub(crate) fn map<'a, F, A, B, P, R>(psr: P, func: F) -> Map<'a, F, A, B, P, R>
where
    F: 'a + Clone + Fn(A) -> B,
    P: Parser<'a, R, Output = A>,
    R: Read,
{
    Map {
        psr,
        func,
        _marker: PhantomData,
    }
}

impl<'a, F, A, B, P, R> Parser<'a, R> for Map<'a, F, A, B, P, R>
where
    F: 'a + Clone + Fn(A) -> B,
    P: Parser<'a, R, Output = A>,
    R: Read,
{
    type Output = B;

    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, B> {
        match self.psr.parse(text, msg_hint) {
            ParseResult::Success(t, pos) => ParseResult::Success((self.func)(t), pos),
            ParseResult::Fail(pos, i, m) => ParseResult::Fail(pos, i, m),
            ParseResult::Error(e) => ParseResult::Error(e),
        }
    }
}

#[derive(Debug)]
pub struct Repeat<'a, O, P, R>
where
    R: Read,
    P: 'a + Parser<'a, R, Output=O>,
{
    lower: usize,
    upper: Option<usize>,
    psr: P,
    _marker: PhantomData<&'a R>,
}

pub(crate) fn repeat<'a,O,P,R>(psr: P, lower: usize, upper: Option<usize>) -> Repeat<'a,O,P,R>
where
    R: Read,
    P: 'a + Parser<'a, R, Output=O>,
{
    Repeat {
        lower,
        upper,
        psr,
        _marker: PhantomData,
    }
}

impl<'a, O, P, R> Clone for Repeat<'a, O, P, R>
where
    R: Read,
    P: 'a + Parser<'a, R, Output=O>,
{
    fn clone(&self) -> Self {
        Repeat {
            lower: self.lower,
            upper: self.upper.clone(),
            psr: self.psr.clone(),
            _marker: PhantomData,
        }
    }
}

impl<'a,O,P,R> Parser<'a, R> for Repeat<'a, O, P, R>
where
    R: Read,
    P: 'a + Parser<'a, R, Output=O>,
{
    type Output = Vec<O>;

    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, Vec<O>> {
        // `pos` is used in various places throughout this function
        let pos = text.pos();

        // If the lower bound is greater than the upper bound, it's not
        // possible to parse. Additionally, the logic later requires this to
        // not be the case.
        if self.upper.is_some() && (self.lower > self.upper.unwrap()) {
            return match msg_hint {
                false => ParseResult::Fail(pos, 0, None),
                true => ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                    format!("{} Lower bound {:?} > upper bound {:?}",
                            "Failed to match pattern repetition",
                            self.lower, self.upper.unwrap())
                }))),
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
                            Some(m) => Some(LazyString::new(move || {
                                format!("{} {:?} {} {:?}. From {}:\n{}",
                                        "Only matched", r, "times, needed at least",
                                        self.lower, p, String::from(m))
                            })),
                            None => Some(LazyString::new(move || {
                                format!("{} {:?} {} {:?} at {} {}.",
                                        "Only matched", r, "times, needed at least",
                                        self.lower, p, "without an additional message")
                            })),
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

pub struct Either<'a, O, P1, P2, R>
where
    P1: 'a + Parser<'a, R, Output=O>,
    P2: 'a + Parser<'a, R, Output=O>,
    R: Read,
{
    left: P1,
    right: P2,
    _marker: PhantomData<&'a R>,
}

impl<'a, O, P1, P2, R> Clone for Either<'a, O, P1, P2, R>
where
    P1: 'a + Parser<'a, R, Output=O>,
    P2: 'a + Parser<'a, R, Output=O>,
    R: Read,
{
    fn clone(&self) -> Self {
        Either {
            left: self.left.clone(),
            right: self.right.clone(),
            _marker: PhantomData,
        }
    }
}

pub(crate) fn either<'a, O, P1, P2, R>(left: P1, right: P2) -> Either<'a, O, P1, P2, R>
where
    P1: 'a + Parser<'a, R, Output=O>,
    P2: 'a + Parser<'a, R, Output=O>,
    R: Read,
{
    Either {
        left,
        right,
        _marker: PhantomData,
    }
}

impl<'a, O, P1, P2, R> Parser<'a, R> for Either<'a, O, P1, P2, R>
where
    P1: 'a + Parser<'a, R, Output=O>,
    P2: 'a + Parser<'a, R, Output=O>,
    R: Read,
{
    type Output = O;

    fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, O> {

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
                    let fmt = |msg: Option<LazyString<'a>>| msg
                        .map(|l| String::from(l))
                        .unwrap_or(String::from("no attached message"));

                    format!("Failed to match either parser:\n  * {}: {}\n  * {}: {}",
                            l_pos, fmt(l_msg), r_pos, fmt(r_msg))
                })));
            },
        };
    }
}

// Section 2: Parsers with macros

// Section 2a: "Any"

mod sealed {
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

pub trait IntoAny<'a, R, P>: sealed::Sealed
where
    P: 'a + Parser<'a, R> + sealed::Sealed,
    R: Read,
{
    fn into(self) -> P;
}

pub(crate) fn any<'a, R, P, A>(into_any: A) -> P
where
    P: 'a + Parser<'a, R> + sealed::Sealed,
    R: Read,
    A: IntoAny<'a, R, P>,
{
    into_any.into()
}

macro_rules! impl_tup_any {
    (
        $any:ident @
        $p:ident @
        $idx:tt
    ) => {
        struct $any<'a, O, R, $p>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
        {
            // Just for ease of use, we're making this one not a tuple
            inner: $p,
            _marker: PhantomData<&'a R>,
        }

        impl<'a, O, R, $p> Clone for $any<'a, O, R, $p>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
        {
            fn clone(&self) -> Self {
                Self {
                    inner: self.inner.clone(),
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, O, R, $p> sealed::Sealed for $any<'a, O, R, $p>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
        {}

        impl<'a, O, R, $p> IntoAny<'a, R, $any<'a, O, R, $p>> for ($p,)
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
            // TODO: why do we need this lifetime bound?
            O: 'a,
        {
            fn into(self) -> $any<'a, O, R, $p> {
                $any {
                    inner: self.0,
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, O, R, $p> Parser<'a, R> for $any<'a, O, R, $p>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
        {
            type Output = O;

            fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, O> {
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
                            let fmt = |msg: Option<LazyString<'a>>| msg
                                .map(|l| String::from(l))
                                .unwrap_or(String::from("no attached message"));

                            format!("Failed to match `any` parser:\n  * {}: {}",
                                    p, fmt(m))
                        })));
                    },
                };
            }
        }
    };

    (
        $any:ident, $($any_tail:ident),+ @
        $p:ident, $($ps:ident),+ @
        $idx:tt @ $($idx_tail:tt)@+
    ) => {
        struct $any<'a, O, R, $p, $($ps),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
            $($ps: 'a + Parser<'a, R, Output=O>),+
        {
            // Note that these are in reverse order, going:
            // PN ... P2, P1
            inner: ($p, $($ps),+),
            _marker: PhantomData<&'a R>,
        }

        impl<'a, O, R, $p, $($ps),+> Clone for $any<'a, O, R, $p, $($ps),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
            $($ps: 'a + Parser<'a, R, Output=O>),+
        {
            fn clone(&self) -> Self {
                let temp = (self.inner.$idx.clone(), $(self.inner.$idx_tail.clone()),+);
                let inner = (temp.$idx, $(temp.$idx_tail),+);

                Self {
                    inner,
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, O, R, $p, $($ps),+> sealed::Sealed for $any<'a, O, R, $p, $($ps),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
            $($ps: 'a + Parser<'a, R, Output=O>),+
        {}

        impl<'a, O, R, $p, $($ps),+> IntoAny<'a, R, $any<'a, O, R, $p, $($ps),+>> for ($p, $($ps),+)
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
            $($ps: 'a + Parser<'a, R, Output=O>),+,
            // TODO: why do we need this lifetime bound?
            O: 'a,
        {
            fn into(self) -> $any<'a, O, R, $p, $($ps),+> {
                $any {
                    inner: self,
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, O, R, $p, $($ps),+> Parser<'a, R> for $any<'a, O, R, $p, $($ps),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output=O>,
            $($ps: 'a + Parser<'a, R, Output=O>),+
        {
            type Output = O;

            fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, O> {
                macro_rules! snd {
                    ( $x:ident, $y:expr ) => { $y }
                }

                let rev_psrs = (&self.inner.$idx, $(&self.inner.$idx_tail),+);
                let mut msgs = (snd!($p, None as Option<LazyString<'a>>),
                    $(snd!($ps, None as Option<LazyString<'a>>)),+);

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
                                            "Higher-order fail encountered from parser",
                                            $idx-$idx_tail, p, String::from(m))
                                }))
                            } else if msg_hint {
                                Some(LazyString::new(move || {
                                    format!("{} #{:?} at {} without message",
                                            "Higher order fail encountered from parser",
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
                        return ParseResult::Fail(pos, 0, Some(LazyString::new(move || {
                            let fmt = |msg: Option<LazyString<'a>>| msg
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

pub trait IntoAll<'a, R, P>: sealed::Sealed
where
    P: 'a + Parser<'a, R> + sealed::Sealed,
    R: Read,
{
    fn into(self) -> P;
}

pub(crate) fn all<'a, R, P, A>(into_all: A) -> P
where
    P: 'a + Parser<'a, R> + sealed::Sealed,
    R: Read,
    A: IntoAll<'a, R, P>,
{
    into_all.into()
}

macro_rules! impl_tup_all {
    (
        $all:ident @
        ($p:ident, $o:ident) @
        $oid:ident, $idx:tt
    ) => {
        struct $all<'a, R, $p, $o>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
        {
            inner: $p,
            _marker: PhantomData<&'a R>,
        }

        impl<'a, R, $p, $o> Clone for $all<'a, R, $p, $o>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
        {
            fn clone(&self) -> Self {
                Self {
                    inner: self.inner.clone(),
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, R, $p, $o> sealed::Sealed for $all<'a, R, $p, $o>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
        {}

        impl<'a, R, $p, $o> IntoAll<'a, R, $all<'a, R, $p, $o>> for ($p,)
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
            $o: 'a,
        {
            fn into(self) -> $all<'a, R, $p, $o> {
                $all {
                    inner: self.0,
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, R, $p, $o> Parser<'a, R> for $all<'a, R, $p, $o>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
        {
            type Output = ($o,);

            fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, Self::Output> {
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

                return ParseResult::Success(($oid,), pos);
            }
        }
    };

    (
        $all:ident, $($all_tail:ident),+ @
        ($p:ident, $o:ident), $(($ps:ident, $os:ident)),+ @
        $oid:ident, $idx:tt @ $($oids:ident, $idx_tail:tt)@+
    ) => {
        struct $all<'a, R, $p, $($ps),+, $o, $($os),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
            $($ps: 'a + Parser<'a, R, Output = $os>),+
        {
            inner: ($p, $($ps),+),
            _marker: PhantomData<&'a R>,
        }

        impl<'a, R, $p, $($ps),+, $o, $($os),+> Clone for $all<'a, R, $p, $($ps),+, $o, $($os),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
            $($ps: 'a + Parser<'a, R, Output = $os>),+
        {
            fn clone(&self) -> Self {
                Self {
                    inner: self.inner.clone(),
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, R, $p, $($ps),+, $o, $($os),+> sealed::Sealed for $all<'a, R, $p, $($ps),+, $o, $($os),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
            $($ps: 'a + Parser<'a, R, Output = $os>),+
        {}

        impl<'a, R, $p, $($ps),+, $o, $($os),+> IntoAll<'a, R, $all<'a, R, $p, $($ps),+, $o, $($os),+>> for ($p,$($ps),+)
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
            $($ps: 'a + Parser<'a, R, Output = $os>,)+
            $o: 'a,
            $($os: 'a,)+
        {
            fn into(self) -> $all<'a, R, $p, $($ps),+, $o, $($os),+> {
                $all {
                    inner: self,
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, R, $p, $($ps),+, $o, $($os),+> Parser<'a, R> for $all<'a, R, $p, $($ps),+, $o, $($os),+>
        where
            R: Read,
            $p: 'a + Parser<'a, R, Output = $o>,
            $($ps: 'a + Parser<'a, R, Output = $os>),+
        {
            type Output = ($o, $($os),+);

            fn parse(&'a self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<'a, Self::Output> {
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

        impl_tup_all! {
            $($all_tail),+ @
            $(($ps, $os)),+ @
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

#[cfg(test)]
mod tests {
    use crate::{Parser, byte_lit, char_lit, string_lit};
    use crate::text::Source;

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
        assert_eq!(psr.parse(&mut src, false).unwrap().0, ("foo", "bar", "baz"));
    }
}
