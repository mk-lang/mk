// TODO: Add more here.
//! The utilities for creating, defining, and using parsers

pub mod bytes;
pub mod text;
mod fundamentals;
mod combinators;
pub mod utils;

use self::{
    utils::{LazyString, Pos},
    text::Source,
};

pub use fundamentals::{
    ByteLiteral,
    ByteRange,
    ByteSeq,
    StringLit,
    CharLit,
    CharRange,
    byte_lit,
    byte_range,
    byte_seq,
    string_lit,
    char_lit,
    char_range,
};

pub use combinators::{
    any,
    all,
    Map,
    Repeat,
    Either,
    DynAny,
};

use std::io::Read;

/// Indicates the outcome of a parsing attempt.
///
/// The methods are all the various deconstructors of the type. The only complex
/// piece of behavior to do with a `ParseResult` is the `i64` in the `Fail`
/// variant. There is information about it [there](#variant.Fail).
#[must_use = "this `ParseResult` may be an `Error` variant, which should be handled"]
pub enum ParseResult<T> {
    /// Indicates a successful parse
    Success(T, Pos),

    /// Indicates that the parser did not find a match.
    ///
    /// A failure message can optionally be supplied, given by the
    /// `Option<LazyString>`; this will be suggested (or not) by the value of
    /// [`msg_hint`] given to the [`Parser`].
    ///
    /// The position of the original failure in the matching process is also
    /// returned - even though this may sometimes be immediately obvious from
    /// context.
    ///
    /// Lastly, the `i64` in the tuple provides the number of nested parsers to
    /// break out of. Some combinators (like `Map`) will simply pass the value,
    /// whereas others (like `Either`) will decrement it, or perform other
    /// operations therein. Typically, a value of 0 indicates a "normal" fail,
    /// values greater than zero cause finitely many nested parsers to fail,
    /// and values less than zero will fail all the way down the stack.
    ///
    /// [`msg_hint`]: trait.Parser.html#tymethod.parse
    /// [`Parser`]: trait.Parser.html
    Fail(Pos, i64, Option<LazyString>),

    /// `Error` indicates that a fatal error has occured while parsing and that
    /// parsing should immediately fail at every level.
    ///
    /// This will usually occur if there was an error reading from a file.
    Error(std::io::Error),
}

impl<T> ParseResult<T> {
    /// Returns whether the `ParseResult` is a `Success` variant
    pub fn is_success(&self) -> bool {
        match self {
            ParseResult::Success(_, _) => true,
            _ => false,
        }
    }

    /// Returns whether the `ParseResult` is a `Fail` variant
    pub fn is_fail(&self) -> bool {
        match self {
            ParseResult::Fail(_, _, _) => true,
            _ => false,
        }
    }

    /// Returns whether the `ParseResult` is a `Error` variant
    pub fn is_error(&self) -> bool {
        match self {
            ParseResult::Error(_) => true,
            _ => false,
        }
    }

    // Internal function for producing error messages
    #[inline(always)]
    fn val_type_str(&self) -> &'static str {
        match self {
            ParseResult::Success(_, _) => "Success",
            ParseResult::Fail(_, _, _) => "Fail",
            ParseResult::Error(_) => "Error",
        }
    }

    /// Unwraps the `Success` value, yielding the inner value and its [position]
    /// in the source
    /// 
    /// [position]: utils/struct.Pos.html
    pub fn unwrap(self) -> (T, Pos) {
        match self {
            ParseResult::Success(t, p) => (t, p),
            _ => panic!(
                "Called `ParseResult::unwrap()` on a `{}` value",
                self.val_type_str()
            ),
        }
    }

    /// Extracts a `Fail` value from the `ParseResult`
    pub fn unwrap_fail(self) -> (Pos, i64, Option<LazyString>) {
        match self {
            ParseResult::Fail(p, i, m) => (p, i, m),
            _ => panic!(
                "Called `ParseResult::unwrap_fail()` on a `{}` value",
                self.val_type_str()
            ),
        }
    }

    /// Extracts an `Error` value from the `ParseResult`
    pub fn unwrap_error(self) -> std::io::Error {
        match self {
            ParseResult::Error(e) => e,
            _ => panic!(
                "Called `ParseResult::unwrap_error()` on a `{}` value",
                self.val_type_str()
            ),
        }
    }
}

/// The backbone of the [`Parser`] trait
///
/// This trait is made distinct in order to allow trait objects - hence the
/// prefix "Dyn". The [`Parser`] trait is a supertrait of `DynParser`, so this
/// is implemented for all `Parsers`.
///
/// Implementing your own parser can be done simply by implementing [`parse`]
/// here.
///
/// [`Parser`]: trait.Parser.html
/// [`parse`]: #tymethod.parse
pub trait DynParser<R: Read> {
    /// The type produced by parsing
    type Output;

    // TODO: Note msg_hint suggests that `ParseResult::Fail` should give `None`.
    //
    // Another note about `msg_hint`: All "fundamental" values will follow this,
    // but combinators may override this when given non-zero fail values
    /// Parses the input text into the output type, consuming bytes as needed
    /// 
    /// This function works as expected - successive (successful) parse attempts
    /// will not consume any more of the `Source` than required.
    /// 
    /// [`ParseResult`]: enum.ParseResult.html
    fn parse(&self, text: &mut Source<R>, msg_hint: bool) -> ParseResult<Self::Output>;
}

// NOTE: None of the functions here are meant to be implemented by anyone else.
// They are all provided in their entirety as "methods" on existing types.
//
// ... something about it being the primary parser trait
// ... something about "the main function is DynParser.parse"
pub trait Parser<R: Read>: DynParser<R> + Sized {
    /// An alias for [`combinators::map`]
    ///
    /// [`combinators::map`]: combinators/fn.map.html
    fn map<B, F>(self, f: F) -> Map<R, F, Self::Output, B, Self>
    where
        F: 'static + Fn(Self::Output) -> B,
    {
        combinators::map(self, f)
    }

    fn repeat(self, lower: usize, upper: Option<usize>) -> Repeat<R, Self::Output, Self> {
        combinators::repeat(self, lower, upper)
    }

    fn or<P>(self, other: P) -> Either<R, Self::Output, Self, P>
    where
        P: Parser<R, Output=Self::Output>,
    {
        combinators::either(self, other)
    }
}
