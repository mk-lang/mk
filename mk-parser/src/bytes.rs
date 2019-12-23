//! Byte manipulation for parsing UTF-8 text

/// Errors from decoding UTF-8 byte sequences
#[derive(Clone, Debug)]
pub enum UTF8Error {
    /// This error will occur when a byte that is not valid in any UTF-8
    /// sequence is encoutered.  A helpful chart of these can be found here:
    /// https://en.wikipedia.org/wiki/UTF-8#Codepage_layout
    Invalid(u8),

    /// This error indicates that the given byte was not the expected next byte
    /// in the sequence: Either a continuation byte (0b10xx_xxxx) was expected
    /// as the next byte in a multiple-character encoding, or the start of a
    /// codepoint (any of: 0b0xxx_xxxx, 0b110x_xxxx, 0b1110_xxxx, or 0b1111_0xxx)
    Unexpected(u8),

    /// Indicates that the length of the given sequence of `Byte`s did not
    /// match the expected number of bytes when decoding.
    ///
    /// This can occur both from an empty slice of bytes and cases where the
    /// leading byte indicated an encoding size that did not match the length
    /// of the slice.
    ///
    /// Only occurs in calls to `Byte::decode_utf8`.
    LengthMismatch(Vec<u8>),
}

/// Returns true if it is any of the following characters:
/// * 0x0A (line feed, '\n')
/// * 0x0B (vertical tab, '\v')
/// * 0x0C (form feed)
/// * 0x0D (carriage return, '\r')
///
/// More information can be found in the documentation for
/// [`Source`](../../trait.Source.html#tymethod.pos) - note that we've excluded
/// U+0085 as its encoding requires multiple bytes.
pub fn is_new_line(b: u8) -> bool {
    b == 0x0A || b == 0x0B || b == 0x0C || b == 0x0D
}

/// Gives the number of bytes expected for a character encoding that starts
/// with this byte. Returns `None` if it is a continuation byte.
///
/// Returns `UTF8Error::Invalid` if the byte can never be part of a UTF-8
/// sequence.
///
/// **Please note:** This function is quick, and so may be used to identify
/// the number of bytes to parse into a character (for use in
/// [`decode_utf8`](#method.decode_utf8))
pub fn expected_utf8_size(b: u8) -> Result<Option<u8>, UTF8Error> {
    const INVALID: u8 = 5;
    const CONT: u8 = 0;

    match UTF8_CHAR_WIDTH[b as usize] {
        INVALID => Err(UTF8Error::Invalid(b)),
        CONT => Ok(None),
        w => Ok(Some(w)),
    }
}

/// Converts the slice of bytes into the corresponding Unicode number,
/// provided that the number of bytes is exactly the amount required.
///
/// For information on errors, see [`UTF8Error`](../enum.UTF8Error.html)
pub fn decode_utf8(bytes: &[u8]) -> Result<u32, UTF8Error> {
    // For this function, refer to section three of the utf-8 definition:
    //
    //     Decoding a UTF-8 character proceeds as follows:
    //
    //     1.  Initialize a binary number with all bits set to 0. Up to 21
    //         bits may be needed.
    //
    //     2.  Determine which bits encode the character number from the
    //         number of octets in the sequence and the second column of the
    //         table above (the bits marked x).
    //
    //     3.  Distribute the bits from the sequence to the binary number,
    //         first the lower-order bits from the last octet of the sequence
    //         and proceeding to the left until no x bits are left. The
    //         binary number is now equal to the character number.
    //
    // The referenced table is:
    //
    //     Char. number range  |        UTF-8 octet sequence
    //        (hexadecimal)    |              (binary)
    //     --------------------+--------------------------------------------
    //     0000 0000-0000 007F | 0xxxxxxx
    //     0000 0080-0000 07FF | 110xxxxx 10xxxxxx
    //     0000 0800-0000 FFFF | 1110xxxx 10xxxxxx 10xxxxxx
    //     0001 0000-0010 FFFF | 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    //
    // The following code should then be fairly self-explanatory.

    if bytes.is_empty() {
        return Err(UTF8Error::LengthMismatch(Vec::from(bytes)));
    }

    let n_opt = expected_utf8_size(bytes[0])?;
    if n_opt.is_none() {
        return Err(UTF8Error::Unexpected(bytes[0]));
    }

    let n = n_opt.unwrap();
    if (n as usize) != bytes.len() {
        return Err(UTF8Error::LengthMismatch(Vec::from(bytes)));
    }

    for &b in bytes[1..].iter() {
        if !is_continuation_byte(b) {
            return Err(UTF8Error::Unexpected(b));
        }
    }

    // We now know that all of the bytes are valid, so we can go ahead and
    // do all of our bit-shifting trickery.

    Ok(match n {
        1 => bytes[0] as u32,
        2 => ((bytes[1] & !CONT_MASK) as u32) + (((bytes[0] & !0b1100_0000) as u32) << 6),
        3 => {
            ((bytes[2] & !CONT_MASK) as u32)
                + (((bytes[1] & !CONT_MASK) as u32) << 6)
                + (((bytes[0] & !0b1110_0000) as u32) << 12)
        }
        4 => {
            ((bytes[3] & !CONT_MASK) as u32)
                + (((bytes[2] & !CONT_MASK) as u32) << 6)
                + (((bytes[1] & !CONT_MASK) as u32) << 12)
                + (((bytes[0] & !0b1111_0000) as u32) << 18)
        }
        _ => panic!("Values outside 1-4 should never occur."),
    })
}

const CONT_MASK: u8 = 0b1100_0000;

// Internal function: Returns whether the byte is a utf-8 continuation byte
fn is_continuation_byte(b: u8) -> bool {
    // For a description, there is a lengthy comment in `decode_utf8`
    b & CONT_MASK == 0b1000_0000
}

/// Returns true if a byte is within the bounds bounds, inclusive
///
/// Literally just:
/// ```no_run
/// # let (b, lower, upper) = (0, 0, 0);
/// # let _ = {
/// b >= lower && b <= upper
/// # };
/// ```
pub fn between_inc(b: u8, lower: u8, upper: u8) -> bool {
    b >= lower && b <= upper
}

/// Checks whether the given byte is between the two characters (inclusive)
///
/// Note that this function expects both characters to be ASCII, and will panic
/// if either is not. The standard library provides a function,
/// [`char::is_ascii`] that can be used to validate input if it is not known at
/// compile-time.
///
/// [`char::is_ascii`]: https://doc.rust-lang.org/std/primitive.char.html#method.is_ascii
pub fn between_chars(b: u8, lower: char, upper: char) -> bool {
    // Hopefully the checking won't produce much overhead, as the bounds are
    // likely to be known at compile-time, and force-inlining should help with that.
    //
    // TODO: Evaluate whether this may be better to make a `const` function
    // simply so that we can guarantee nice optimizations
    if !lower.is_ascii() {
        panic!(
            "Lower bound '{}' (U+{}) is not ascii - it must be",
            lower, lower as u32
        );
    } else if !upper.is_ascii() {
        panic!(
            "Upper bound '{}' (U+{}) is not ascii - it must be",
            lower, lower as u32
        );
    }

    // Because ascii values all fit within a byte, we're now safe to convert
    use std::convert::TryFrom;
    b >= u8::try_from(lower as u32).unwrap() && b <= u8::try_from(upper as u32).unwrap()
}

pub fn in_range<R: std::ops::RangeBounds<u8>>(b: u8, range: R) -> bool {
    use std::ops::Bound::*;
    let lower = match range.start_bound() {
        Included(&b) => b,
        Excluded(&b) => {
            if b == std::u8::MAX {
                return false;
            }

            b + 1
        }
        Unbounded => std::u8::MIN,
    };

    let upper = match range.end_bound() {
        Included(&b) => b,
        Excluded(&b) => {
            if b == std::u8::MIN {
                return false;
            }

            b - 1
        }
        Unbounded => std::u8::MIN,
    };

    b >= lower && b <= upper
}

// Inspired by a similar array in the rust source, at
// src/core/str/mod.sr, line 1566
//
// Where the the file above gives both continuation bytes and invalid bytes a
// value of 0, we're instead giving invalid bytes an expected length of 5,
// which is not possible in utf-8. We're basing this on a chart from wikipedia:
//   https://en.wikipedia.org/wiki/UTF-8#Codepage_layout
//
// We make it static (not const) because it makes no difference in the runtime:
// they both will require the same pointer arithmetic. The only difference is
// in the size of the compiled binary, which will be larger if it is declared
// as `const`.
static UTF8_CHAR_WIDTH: [u8; 256] = [
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    5, 5, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_all() {
        // each element of cases is:
        let chars = ['a', '(', '❤', '☆', '£', '≨'];

        for &c in chars.iter() {
            let mut byte_buf = [0u8, 0, 0, 0];
            let bytes = c.encode_utf8(&mut byte_buf).as_bytes();

            let err_msg = format!(
                "{}{}",
                format!("Failed to decode bytes for character '{}':\n", c),
                format!("\tChar byte values: {:?}", &bytes)
            );
            let n = decode_utf8(&bytes).expect(&err_msg);

            use std::convert::TryInto;
            let err_msg = format!(
                "Decoding character '{}' gave an invalid unicode number {}, expected {}",
                c, n, c as u32
            );
            let c_: char = n.try_into().expect(&err_msg);

            assert_eq!(c, c_, "Processing '{}' gave '{}' (U+{})", c, c_, n);
        }
    }
}
