//! Defines [`Pos`] and [`LazyString`]
//!
//! **Note**: Due to the current limitations of rust-doc, the links above only
//! work from the crate root. ☹
//!
//! [`Pos`]: utils/struct.Pos.html
//! [`LazyString`]: utils/struct.LazyString.html

use std::fmt::{self, Display, Formatter};

/// A single-use, lazily-evaluated string.
///
/// # Usage
///
/// Typically, `LazyString`s will be constructed with a closure in the following
/// manner:
/// ```
/// # use mk_parser::utils::LazyString;
/// use std::string::ToString;
///
/// let x: i32 = 3;
///
/// let lazy = LazyString::new(move || {
///     x.to_string()
/// });
/// ```
/// And consumed by:
/// println!("{}", lazy.into());
///
/// The advantage of this type is that it delays (sometimes moderately
/// expensive) string conversion until we actually need it - there are many
/// points where we may not no whether a failure message is needed until after
/// the computation that would produce it has finished.
///
/// This type is the failure message type used in [`ParseResult`].
///
/// [`ParseResult`]: ../enum.ParseResult.html
pub struct LazyString(Box<dyn 'static + FnOnce() -> String>);

impl From<LazyString> for String {
    fn from(lazy: LazyString) -> String {
        lazy.0()
    }
}

impl LazyString {
    /// Creates a new `LazyString`
    pub fn new<F: 'static + FnOnce() -> String>(f: F) -> LazyString {
        LazyString(Box::new(f))
    }
}

/// Represents the position of a byte in a [`Source`].
///
/// Note that this distinctly counts **bytes**, not unicode characters.
///
/// For convenience, `From<(u32, u32)>` is implemented for `Pos`: the first
/// value gives the line, and the second gives the column.
///
/// [`Source`]: ../source/struct.Source.html
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pos {
    // Deriving PartialOrd and Ord only works because `line` is before `col`.
    // Per the documentation for PartialOrd:
    // "When derived on structs, it will produce a lexicographic ordering based
    //  on the top-to-bottom declaration order of the struct's members"
    /// The line in the source
    pub line: u32,

    /// The column (by bytes - not characters) in the source
    pub col: u32,
}

impl From<(u32, u32)> for Pos {
    fn from(t: (u32, u32)) -> Pos {
        Pos {
            line: t.0,
            col: t.1,
        }
    }
}

impl Display for Pos {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[cfg(test)]
mod tests {
    use super::Pos;
    use std::cmp::Ord;

    #[test]
    fn lazy_string() {
        let foo = || String::from("foo");
        let lazy = super::LazyString::new(foo);
        assert_eq!(String::from(lazy), "foo");
    }

    #[test]
    fn tuple_into_pos() {
        let pos = Pos { line: 4, col: 6 };
        assert_eq!(pos, Pos::from((4, 6)));
    }

    #[test]
    fn pos_order() {
        // All we're doing here is checking that `Pos` will have the correct
        // ordering

        let tab: Vec<((u32, u32), (u32, u32))> = vec![
            ((1, 1), (1, 3)),
            ((1, 2), (1, 2)),
            ((3, 1), (4, 1)),
            ((3, 4), (5, 2)),
        ];

        for (i, (p1, p2)) in tab.iter().enumerate() {
            let exp_left = p1.cmp(p2);
            let exp_right = p2.cmp(p1);

            let pos1: Pos = (*p1).into();
            let pos2: Pos = (*p2).into();

            assert_eq!(exp_left, pos1.cmp(&pos2), "From iteration {}", i);
            assert_eq!(exp_right, pos2.cmp(&pos1), "From iteration {}", i);
        }
    }
}
