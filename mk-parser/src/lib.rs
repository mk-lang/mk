// TODO-DOC: Add more here: examples and general descriptions
// TODO-DOC: Add a note about bnf-syntax feature
//! The utilities for creating, defining, and using parsers

// Personal preference - It often aligns better, and can be more
// concise than a typical "if" statement.
#![allow(clippy::match_bool)]
// Set a url for allowing "run" buttons on our doc examples
// TODO: This won't work until we release the crate
#![doc(html_playground_url = "https://play.rust-lang.org/")]

// General TODO: Reduce repeated code in failure messages to use macro(s)
// General TODO: Audit doc examples to use the same ordering of imports
// --> Maybe we include a prelude?

#[cfg(feature = "bnf-syntax")]
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

use combinators::{Chain, Either, Map, Repeat};
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
    /// # Failure level
    ///
    /// The `i64` in the tuple provides the failure level, which is
    /// symbolically the number of nested parsers to break out of. Some
    /// combinators (like [`Map`]) will simply pass the value, whereas others
    /// (like [`Either`]) will decrement it.
    /// Typically, a value of 0 indicates a "normal" fail, values greater than
    /// zero cause finitely many nested parsers to fail, and values less than
    /// zero will fail all the way down the stack of parsers.
    ///
    /// For setting the failure level, see [`Parser::expect`],
    /// [`Parser::require`], and [`Handlers::FailLevel`].
    ///
    /// [`msg_hint`]: trait.Parser.html#tymethod.parse
    /// [`Parser`]: trait.Parser.html
    /// [`Map`]: combinators/struct.Map.html
    /// [`Either`]: combinators/struct.Either.html
    /// [`Parser::expect`]: trait.Parser.html#method.expect
    /// [`Parser::require`]: trait.Parser.html#method.require
    /// [`Handlers::FailLevel`]: handlers/struct.FailLevel.html
    // TODO: Improve the explanation of failure level
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
        combinators::Map { psr: self, func: f }
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

    /// Shorthand for constructing [`combinators::Either`]
    ///
    /// `Either` will match on inputs where either the first or the second
    /// match - preferring the first. `Parser::or` will likewise attempt to
    /// match `self` over its argument.
    ///
    /// For more information, see [`Either`].
    ///
    /// [`combinators::Either`]: combinators/struct.Either.html
    /// [`Either`]: combinators/struct.Either.html
    fn or<P>(self, other: P) -> Either<Self, P>
    where
        P: Parser<Output = Self::Output>,
    {
        Either {
            left: self,
            right: other,
        }
    }

    /// Shorthand for constructing [`combinators::Chain`]
    ///
    /// `Chain` will create a parser which matches only on a match of the
    /// first, followed by the second.
    ///
    /// For more information, see [`Chain`].
    ///
    /// [`combinators::Chain`]: combinators/struct.Chain.html
    /// [`Chain`]: combinators/struct.Chain.html
    fn and<P>(self, other: P) -> Chain<Self, P>
    where
        P: Parser,
    {
        Chain {
            first: self,
            second: other,
        }
    }

    /// Shorthand for constructing [`handlers::Named`]
    ///
    /// Names the parser so that failure messages can include some unique,
    /// helpful information.
    ///
    /// For more information, see [`Named`].
    ///
    /// [`handlers::Named`]: handlers/struct.Named.html
    /// [`Named`]: handlers/struct.Named.html
    fn name<S: Into<String>>(self, name: S) -> Named<Self> {
        handlers::Named {
            psr: self,
            name: name.into(),
        }
    }

    /// Modifies the failure level of the parser so that containing parsers will
    /// fail if it is not met
    ///
    /// The "level" value returned with any failure will be modified so that it
    /// will always increase the level value to one (if it is already greater,
    /// that is preserved).
    ///
    /// For more information, see [`handlers::FailLevel`], the associated
    /// function [`fail_level`], and general failure information in
    /// [`ParseResult::Fail`].
    ///
    /// [`handlers::FailLevel`]: handlers/struct.FailLevel.html
    /// [`fail_level`]: handlers/fn.fail_level.html
    /// [`ParseResult::Fail`]: enum.ParseResult.html#variant.Fail
    fn expect(self) -> FailLevel<Self, fn(i64) -> i64> {
        handlers::fail_level(self, |l| if l == 0 { 1_i64 } else { l })
    }

    /// Modifies the parser to cause a fail at every level if not matched
    ///
    /// Internally, this sets the "level" of the failure to -1.
    ///
    /// For more information, see [`handlers::FailLevel`], the associated
    /// function [`fail_level`], and general failure information in
    /// [`ParseResult::Fail`].
    ///
    /// [`handlers::FailLevel`]: handlers/struct.FailLevel.html
    /// [`fail_level`]: handlers/fn.fail_level.html
    /// [`ParseResult::Fail`]: enum.ParseResult.html#variant.Fail
    fn require(self) -> FailLevel<Self, fn(i64) -> i64> {
        handlers::fail_level(self, |_| -1_i64)
    }
}
