// TODO-DOC: Add more here: examples and general descriptions
//! The utilities for creating, defining, and using parsers

// Personal preference - It often aligns better, and can be more
// concise than a typical "if" statement.
#![allow(clippy::match_bool)]

// Set a url for allowing "run" buttons on our doc examples
// TODO: This won't work until we release the crate
#![doc(html_playground_url = "https://play.rust-lang.org/")]

#[macro_use]
mod macros;

pub mod bytes;
pub mod source;
pub mod utils;

pub mod basics;
pub mod combinators;
pub mod fundamentals;
pub mod handlers;

use self::{
    source::Source,
    utils::{LazyString, Pos},
};

use combinators::{Map, Repeat, Either, Chain};
use handlers::{FailLevel, Named};

/// Indicates the outcome of a parsing attempt.
///
/// The methods are all the various deconstructors of the type. The only complex
/// piece of behavior to do with a `ParseResult` is the `i64` in the `Fail`
/// variant. There is information about it [there](#variant.Fail).
#[must_use = "this `ParseResult` may be an `Error` variant, which should be handled"]
pub enum ParseResult<T> {
    /// Indicates a successful parse
    ///
    /// Gives the output type and the position it was found at
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
/// here and using the default implementation of [`Parser`].
///
/// [`Parser`]: trait.Parser.html
/// [`parse`]: #tymethod.parse
pub trait DynParser {
    /// The type produced by parsing
    type Output;

    /// Parses the input source into the output type, consuming bytes as needed
    ///
    /// This function works as expected - successive (successful) parse attempts
    /// will not consume any more of the `Source` than required.
    ///
    /// `msg_hint` serves as a suggestion for whether to provide a failure
    /// message; i.e. whether the [`Fail`] variant of the result should be
    /// `Some(LazyString(...))`. If true, a failure message has been requested.
    ///
    /// Note that all "fundamental" and "basic" parsers will respect `msg_hint`
    /// in its entirety, but some combinators may not: If one of the parsers
    /// they depend upon fails with a non-zero failure level AND has a message,
    /// they they will override `msg_hint` and wrap the failure message anyways.
    ///
    /// [`ParseResult`]: enum.ParseResult.html
    /// [`Fail`]: enum.ParseResult.html#variant.Fail
    fn parse(&self, src: &mut Source, msg_hint: bool) -> ParseResult<Self::Output>;
}

/// The primary parsing trait
///
/// This trait exists in concert with [`DynParser`] to provide all of the
/// methods on various types. The core functionality comes from
/// `DynParser::parse()`, but most of the combinators require their arguments
/// to be `Sized` - hence the existence of this trait.
///
/// Examples are provided at the crate root.
///
/// If you are implementing your own parser (a rare case!), there will likely
/// be no reason to override the default method implementations here. They are
/// used only to provide syntactic elegance to the functionality of the crate.
///
/// [`DynParser`]: trait.DynParser.html
pub trait Parser: DynParser + Sized {

    /// Shorthand for constructing [`combinators::Map`]
    ///
    /// `Map` will apply `f` to to the output of this parser.
    ///
    /// [`combinators::Map`]: combinators/struct.Map.html
    fn map<F, T>(self, f: F) -> Map<Self, F, T>
    where
        F: 'static + Fn(Self::Output) -> T,
    {
        combinators::Map {
            psr: self,
            func: f,
        }
    }

    /// Shorthand for constructing [`combinators::Repeat`]
    ///
    /// The lower bound indicates the minimum required number of repetitions to
    /// have a successful parse, and the upper bound - if present - indicates
    /// the maximum allowed number of repetitions. If `lower` is greater than
    /// `upper`, the parser will never match.
    ///
    /// For more information, see [`Repeat`].
    ///
    /// [`combinators::Repeat`]: combinators/struct.Repeat.html
    /// [`Repeat`]: combinators/struct.Repeat.html
    fn repeat(self, lower: usize, upper: Option<usize>) -> Repeat<Self> {
        Repeat {
            lower,
            upper,
            psr: self,
        }
    }

    // TODO-DOC
    fn or<P>(self, other: P) -> Either<Self, P>
    where
        P: Parser<Output = Self::Output>,
    {
        Either {
            left: self,
            right: other,
        }
    }

    // TODO-DOC
    fn and<P>(self, other: P) -> Chain<Self, P>
    where
        P: Parser,
    {
        Chain {
            first: self,
            second: other,
        }
    }

    /// An alias for [`handlers::named`]
    ///
    /// [`handlers::named`]: handlers/fn.named.html
    // TODO-DOC: Add example(s)
    fn name<S: Into<String>>(self, name: S) -> Named<Self> {
        handlers::named(self, name.into())
    }

    // TODO-DOC
    fn expect(self) -> FailLevel<Self, fn(i64) -> i64> {
        handlers::fail_level(self, |_| 1_i64)
    }

    // TODO-DOC
    fn require(self) -> FailLevel<Self, fn(i64) -> i64> {
        handlers::fail_level(self, |_| -1_i64)
    }
}

