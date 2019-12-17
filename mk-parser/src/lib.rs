//! The utilities for creating, defining, and using parsers

// TODO: Document
pub mod bytes;
pub mod text;
mod combinators;
mod fundamentals;

// For those searching, these each contain:
// Combinators:
// * Map, Repeat, Either
// Fundamentals:
// * ByteLiteral, ByteRange, ByteSeq, StringLit, CharLit, CharRange
pub use combinators::*;
pub use fundamentals::*;

use std::fmt::{self, Display, Formatter};
use std::io::Read;

pub struct LazyString<'a>(Box<dyn 'a + FnOnce() -> String>);

impl From<LazyString<'_>> for String {
    fn from(lazy: LazyString) -> String {
        lazy.0()
    }
}

impl<'a> LazyString<'a> {
    pub fn new<F: 'a + FnOnce() -> String>(f: F) -> LazyString<'a> {
        LazyString(Box::new(f))
    }
}

// TODO: Document
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pos {
    // Deriving PartialOrd and Ord only works because `line` is before `col`.
    // Per the documentation for PartialOrd:
    // "When derived on structs, it will produce a lexicographic ordering based
    //  on the top-to-bottom declaration order of the struct's members"
    pub line: u32,
    pub col: u32,
}

impl Display for Pos {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

pub enum ParseResult<'a, T> {
    /// Indicates a successful parse
    Success(T, Pos),

    /// `Fail` indicates that there was no parse result found, and gives the
    /// number of nested combinators to break out of. Negative values will
    /// have the effect of failing through the entire stack (unless some other
    /// parser later handles it). This value is usually zero.
    ///
    /// The provided `String` gives an attached error message, if it is
    /// applicable.
    Fail(Pos, i64, Option<LazyString<'a>>),

    /// `Error` indicates that a fatal error has occured while parsing and that
    /// parsing should immediately fail at every level.
    Error(std::io::Error),
}

impl<'a, T> ParseResult<'a, T> {
    pub fn is_error(&self) -> bool {
        match self {
            ParseResult::Error(_) => true,
            _ => false,
        }
    }

    pub fn is_fail(&self) -> bool {
        match self {
            ParseResult::Fail(_, _, _) => true,
            _ => false,
        }
    }

    pub fn is_success(&self) -> bool {
        match self {
            ParseResult::Success(_, _) => true,
            _ => false,
        }
    }

    fn val_type_str(&self) -> &'static str {
        match self {
            ParseResult::Success(_, _) => "Success",
            ParseResult::Fail(_, _, _) => "Fail",
            ParseResult::Error(_) => "Error",
        }
    }

    pub fn unwrap_error(self) -> std::io::Error {
        match self {
            ParseResult::Error(e) => e,
            _ => panic!(
                "Called `ParseResult::unwrap_error()` on a `{}` value",
                self.val_type_str()
            ),
        }
    }

    pub fn unwrap_fail(self) -> (Pos, i64, Option<LazyString<'a>>) {
        match self {
            ParseResult::Fail(p, i, m) => (p, i, m),
            _ => panic!(
                "Called `ParseResult::unwrap_fail()` on a `{}` value",
                self.val_type_str()
            ),
        }
    }

    pub fn unwrap(self) -> (T, Pos) {
        match self {
            ParseResult::Success(t, p) => (t, p),
            _ => panic!(
                "Called `ParseResult::unwrap()` on a `{}` value",
                self.val_type_str()
            ),
        }
    }
}

// TODO: Do we actually need Clone?
pub trait Parser<'a, R: Read>: Clone {
    type Output;

    // TODO: Note msg_hint suggests that `ParseResult::Fail` should give `None`.
    // Also note that this is the only function that should be implemented. All
    // provided functions should not be altered.
    //
    // Another note about `msg_hint`: All "fundamental" values will
    fn parse(
        &'a self,
        text: &mut text::Source<R>,
        msg_hint: bool,
    ) -> ParseResult<'a, Self::Output>;

    // TODO: Document
    fn map<B, F>(self, f: F) -> Map<'a, F, Self::Output, B, Self, R>
    where
        F: 'a + Clone + Fn(Self::Output) -> B,
    {
        combinators::map(self, f)
    }

    // TODO: Document
    fn repeat(self, lower: usize, upper: Option<usize>) -> Repeat<'a, Self::Output, Self, R> {
        combinators::repeat(self, lower, upper)
    }

    // TODO: Document
    fn or<P>(self, other: P) -> Either<'a, Self::Output, Self, P, R>
    where
        P: Parser<'a, R, Output=Self::Output>
    {
        combinators::either(self, other)
    }
}

impl<'a, R, F, O> Parser<'a, R> for F
where
    R: Read,
    F: 'a + Fn(&mut text::Source<R>, bool) -> ParseResult<'a, O> + Clone,
{
    type Output = O;

    fn parse(&self, text: &mut text::Source<R>, msg_hint: bool) -> ParseResult<'a, O> {
        self(text, msg_hint)
    }
}
