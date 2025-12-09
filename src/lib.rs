//! A safe, memory-safe Rust implementation of C's `sscanf` function.
//!
//! This library provides format string parsing functionality similar to C's scanf family,
//! but with Rust's safety guarantees - no buffer overflows, no undefined behavior.
//!
//! # Supported Format Specifiers
//!
//! ## Integer Conversions
//! - `%d` - Signed decimal integer
//! - `%i` - Signed integer with auto-detection (base 10, 8 for '0' prefix, 16 for '0x'/'0X' prefix)
//! - `%o` - Unsigned octal integer
//! - `%u` - Unsigned decimal integer
//! - `%x`, `%X` - Unsigned hexadecimal integer
//!
//! ## Floating-Point Conversions
//! - `%f`, `%F`, `%e`, `%E`, `%g`, `%G`, `%a`, `%A` - Floating-point number
//!
//! ## Character/String Conversions
//! - `%c` - Fixed number of characters (default 1)
//! - `%s` - Sequence of non-whitespace characters
//! - `%[...]` - Character set matching
//! - `%[^...]` - Inverted character set matching
//!
//! ## Special Conversions
//! - `%n` - Store number of characters consumed so far
//! - `%%` - Literal percent sign
//!
//! # Modifiers
//!
//! ## Assignment Suppression
//! - `*` - Suppresses assignment; conversion happens but result is discarded
//!
//! ## Length Modifiers
//! - `hh` - char (for integer conversions)
//! - `h` - short int (for integer conversions)
//! - `l` - long int (for integers), double (for floats)
//! - `ll` - long long int (for integer conversions)
//! - `L` - long double (for float conversions)
//! - `j` - intmax_t (for integer conversions)
//! - `t` - ptrdiff_t (for integer conversions)
//! - `z` - size_t (for integer conversions)
//!
//! ## Field Width
//! - Decimal integer between `%` and conversion specifier limits maximum bytes scanned
//!
//! # Example
//!
//! ```
//! use xj_scanf::{scanf_str, ScanValue};
//!
//! let values = scanf_str("42 3.14 hello", "%d %f %s").unwrap();
//! assert_eq!(values.len(), 3);
//! ```
//!
//! # Error Handling
//!
//! Unlike C's sscanf which returns magic values, this implementation uses proper
//! `Result` types:
//! - `Ok((values, count))` - Successful parse with assigned values and count
//! - `Err(ScanError::Eof)` - Input exhausted before first conversion
//! - `Err(ScanError::MatchFailure)` - Input doesn't match format
//! - `Err(ScanError::InvalidFormat)` - Malformed format string
//!
//! # Safety
//!
//! This implementation avoids all undefined behavior present in C's sscanf:
//! - No buffer overflows - all bounds are checked
//! - No null pointer issues - Rust's type system prevents this
//! - No type mismatches - values are returned as typed enums

pub mod legacy;

use std::fmt;
use std::io::BufRead;

/// Errors that can occur during scanf operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScanError {
    /// The format string is malformed (e.g., incomplete conversion specifier,
    /// unclosed bracket in character set, or unsupported conversion like `%p`).
    InvalidFormat,
    /// Input does not match the expected format (e.g., trying to parse "abc" as `%d`).
    MatchFailure,
    /// End of input reached before any conversion could complete.
    Eof,
}

impl fmt::Display for ScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScanError::InvalidFormat => write!(f, "Invalid format string"),
            ScanError::MatchFailure => write!(f, "Input does not match format"),
            ScanError::Eof => write!(f, "End of input reached"),
        }
    }
}

impl std::error::Error for ScanError {}

/// A type alias for Results with [`ScanError`].
pub type ScanResult<T> = Result<T, ScanError>;

/// Length modifiers that affect the size/type of the converted value.
///
/// These correspond to C's length modifiers like `h`, `l`, `ll`, etc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LengthModifier {
    /// No length modifier specified (default sizes: int, float).
    None,
    /// `hh` - char-sized integer.
    Hh,
    /// `h` - short int.
    H,
    /// `l` - long int for integers, double for floats.
    L,
    /// `ll` - long long int.
    Ll,
    /// `j` - intmax_t (maximum width integer).
    J,
    /// `z` - size_t.
    Z,
    /// `t` - ptrdiff_t.
    T,
}

/// The type of conversion to perform, parsed from a format specifier.
///
/// Each variant corresponds to a conversion specifier in the format string
/// (e.g., `%d`, `%s`, `%[...]`).
#[derive(Debug, Clone)]
pub enum ConversionSpec {
    /// `%d` - Signed decimal integer.
    SignedInt(LengthModifier),
    /// `%u` - Unsigned decimal integer.
    UnsignedInt(LengthModifier),
    /// `%o` - Unsigned octal integer.
    OctalInt(LengthModifier),
    /// `%x` or `%X` - Unsigned hexadecimal integer.
    HexInt(LengthModifier),
    /// `%i` - Signed integer with auto-detected base (10, 8, or 16).
    AutoInt(LengthModifier),
    /// `%f`, `%e`, `%g`, `%a` (and uppercase variants) - Floating-point number.
    Float(LengthModifier),
    /// `%s` - Sequence of non-whitespace characters (null-terminated in C).
    String,
    /// `%c` - Read a fixed number of characters (default 1, does NOT skip whitespace).
    Char(usize),
    /// `%[...]` or `%[^...]` - Character set matching.
    CharSet {
        /// If true, matches characters NOT in the set (`%[^...]`).
        inverted: bool,
        /// The expanded set of characters to match against.
        chars: String,
    },
    /// `%p` - Pointer value (not implemented, returns InvalidFormat).
    Pointer,
    /// `%n` - Store the number of characters consumed so far (does not consume input).
    Position,
    /// A literal character that must match exactly in the input.
    Literal(char),
    /// `%%` - Matches a literal percent sign in the input.
    Percent,
}

/// A parsed format specifier with all its components.
///
/// Represents a single conversion directive from the format string,
/// including any modifiers like suppression (`*`) or field width.
#[derive(Debug)]
pub struct FormatSpec {
    /// If true, the conversion is performed but the result is discarded (`*` modifier).
    pub suppress: bool,
    /// Maximum field width (number of input characters to consume for this conversion).
    pub width: Option<usize>,
    /// The type of conversion to perform.
    pub conversion: ConversionSpec,
}

/// A value scanned from input, with its type determined by the conversion specifier.
///
/// Unlike C's sscanf which writes to caller-provided pointers of specific types,
/// this implementation returns typed values that the caller can match on.
#[derive(Debug, PartialEq)]
pub enum ScanValue {
    /// 32-bit signed integer (from `%d`, `%i` without length modifier).
    I32(i32),
    /// 64-bit signed integer (from `%d`, `%i` with `l` or `ll` modifier).
    I64(i64),
    /// 32-bit unsigned integer (from `%u`, `%o`, `%x` without length modifier).
    U32(u32),
    /// 64-bit unsigned integer (from `%u`, `%o`, `%x` with `l` or `ll` modifier).
    U64(u64),
    /// 32-bit float (from `%f`, `%e`, `%g`, `%a` without `L` modifier).
    F32(f32),
    /// 64-bit float (from `%f`, `%e`, `%g`, `%a` with `L` or `l` modifier).
    F64(f64),
    /// String (from `%s` or `%[...]`).
    String(String),
    /// Single character (from `%c` with default width of 1).
    Char(char),
    /// Multiple characters as bytes (from `%c` with width > 1).
    Chars(Vec<u8>),
    /// Position in input (from `%n` - number of bytes consumed so far).
    Position(usize),
}

/// Internal parser state for processing input during scanf operations.
struct Parser<R> {
    /// The buffered reader to read from.
    reader: R,
    /// Peeked byte (if any).
    peeked: Option<u8>,
    /// Number of bytes consumed so far.
    pos: usize,
}

impl<R: BufRead> Parser<R> {
    fn new(reader: R) -> Self {
        Parser {
            reader,
            peeked: None,
            pos: 0,
        }
    }

    fn peek(&mut self) -> Option<u8> {
        if self.peeked.is_some() {
            return self.peeked;
        }
        match self.reader.fill_buf() {
            Ok(buf) if !buf.is_empty() => {
                self.peeked = Some(buf[0]);
                self.peeked
            }
            _ => None,
        }
    }

    fn consume(&mut self) -> Option<u8> {
        let byte = if let Some(b) = self.peeked.take() {
            Some(b)
        } else {
            match self.reader.fill_buf() {
                Ok(buf) if !buf.is_empty() => Some(buf[0]),
                _ => None,
            }
        };
        if byte.is_some() {
            self.reader.consume(1);
            self.pos += 1;
        }
        byte
    }

    fn unconsume(&mut self, byte: u8) {
        debug_assert!(self.peeked.is_none(), "Cannot unconsume when peeked is set");
        self.peeked = Some(byte);
        self.pos -= 1;
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_ascii_whitespace() {
                self.consume();
            } else {
                break;
            }
        }
    }

    fn read_int(&mut self, width: Option<usize>, base: u32, signed: bool) -> ScanResult<String> {
        let max_width = width.unwrap_or(usize::MAX);
        let mut result = String::new();
        let mut count = 0;

        // Handle optional sign
        if let Some(ch) = self.peek() {
            if ch == b'+' || (ch == b'-' && signed) {
                result.push(ch as char);
                self.consume();
                count += 1;
            }
        }

        // Handle 0x prefix for hex
        if base == 16 && count < max_width && self.peek() == Some(b'0') {
            result.push('0');
            self.consume();
            count += 1;

            if count < max_width && (self.peek() == Some(b'x') || self.peek() == Some(b'X')) {
                result.push(self.consume().unwrap() as char);
                count += 1;
            }
        }

        // Read digits
        let mut found_digit = false;
        while count < max_width {
            if let Some(ch) = self.peek() {
                let digit_char = ch as char;
                if digit_char.is_digit(base) {
                    result.push(digit_char);
                    self.consume();
                    count += 1;
                    found_digit = true;
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        if !found_digit {
            return Err(ScanError::MatchFailure);
        }

        Ok(result)
    }

    fn read_auto_int(&mut self, width: Option<usize>, signed: bool) -> ScanResult<(String, u32)> {
        let max_width = width.unwrap_or(usize::MAX);
        let mut result = String::new();
        let mut count = 0;

        // Handle optional sign
        if let Some(ch) = self.peek() {
            if ch == b'+' || (ch == b'-' && signed) {
                result.push(ch as char);
                self.consume();
                count += 1;
            }
        }

        // Detect base
        let base = if self.peek() == Some(b'0') && count < max_width {
            result.push('0');
            self.consume();
            count += 1;

            if count < max_width {
                match self.peek() {
                    Some(b'x') | Some(b'X') => {
                        result.push(self.consume().unwrap() as char);
                        count += 1;
                        16
                    }
                    Some(ch) if (ch as char).is_digit(8) => 8,
                    _ => 10,
                }
            } else {
                10
            }
        } else {
            10
        };

        // Read remaining digits
        let mut found_digit = result.len() > 0 && result.chars().last().unwrap().is_digit(base);
        while count < max_width {
            if let Some(ch) = self.peek() {
                let digit_char = ch as char;
                if digit_char.is_digit(base) {
                    result.push(digit_char);
                    self.consume();
                    count += 1;
                    found_digit = true;
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        if !found_digit {
            return Err(ScanError::MatchFailure);
        }

        Ok((result, base))
    }

    fn read_float(&mut self, width: Option<usize>) -> ScanResult<String> {
        let max_width = width.unwrap_or(usize::MAX);
        let mut result = String::new();
        let mut count = 0;

        // Handle sign
        if let Some(ch) = self.peek() {
            if ch == b'+' || ch == b'-' {
                result.push(ch as char);
                self.consume();
                count += 1;
            }
        }

        let mut found_digit = false;
        let mut found_dot = false;
        let mut found_exp = false;

        while count < max_width {
            match self.peek() {
                Some(ch @ b'0'..=b'9') => {
                    result.push(ch as char);
                    self.consume();
                    count += 1;
                    found_digit = true;
                }
                Some(b'.') if !found_dot && !found_exp => {
                    result.push('.');
                    self.consume();
                    count += 1;
                    found_dot = true;
                }
                Some(ch @ (b'e' | b'E')) if found_digit && !found_exp => {
                    result.push(ch as char);
                    self.consume();
                    count += 1;
                    found_exp = true;
                    // Handle exponent sign
                    if count < max_width {
                        if let Some(sign @ (b'+' | b'-')) = self.peek() {
                            result.push(sign as char);
                            self.consume();
                            count += 1;
                        }
                    }
                }
                _ => break,
            }
        }

        if !found_digit {
            return Err(ScanError::MatchFailure);
        }

        Ok(result)
    }

    fn read_string(&mut self, width: Option<usize>) -> ScanResult<String> {
        let max_width = width.unwrap_or(usize::MAX);
        let mut result = String::new();
        let mut count = 0;

        while count < max_width {
            match self.peek() {
                Some(ch) if !ch.is_ascii_whitespace() => {
                    result.push(ch as char);
                    self.consume();
                    count += 1;
                }
                _ => break,
            }
        }

        if result.is_empty() {
            return Err(ScanError::MatchFailure);
        }

        Ok(result)
    }

    fn read_chars(&mut self, count: usize) -> ScanResult<Vec<u8>> {
        let mut result = Vec::new();
        for _ in 0..count {
            if let Some(ch) = self.consume() {
                result.push(ch);
            } else {
                return Err(ScanError::Eof);
            }
        }
        Ok(result)
    }

    fn read_charset(
        &mut self,
        inverted: bool,
        charset: &str,
        width: Option<usize>,
    ) -> ScanResult<String> {
        let max_width = width.unwrap_or(usize::MAX);
        let mut result = String::new();
        let mut count = 0;

        while count < max_width {
            match self.peek() {
                Some(ch) => {
                    let char_ch = ch as char;
                    let in_set = charset.contains(char_ch);
                    if in_set != inverted {
                        result.push(char_ch);
                        self.consume();
                        count += 1;
                    } else {
                        break;
                    }
                }
                None => break,
            }
        }

        if result.is_empty() {
            return Err(ScanError::MatchFailure);
        }

        Ok(result)
    }
}

/// Parses a scanf format string into a sequence of format specifications.
///
/// # Arguments
///
/// * `format` - A format string using scanf-style conversion specifiers.
///
/// # Returns
///
/// A vector of [`FormatSpec`] on success, or [`ScanError::InvalidFormat`] if
/// the format string is malformed.
///
/// # Example
///
/// ```
/// use xj_scanf::parse_format;
///
/// let specs = parse_format("%d  %s").unwrap();
/// assert_eq!(specs.len(), 4); // %d, space, space, %s
/// assert_eq!(specs[1].width, None);
/// assert_eq!(specs[1].suppress, false);
/// assert_eq!(format!("{:?}", specs[1].conversion), "Literal(' ')");
/// ```
pub fn parse_format(format: &str) -> ScanResult<Vec<FormatSpec>> {
    let mut specs = Vec::new();
    let mut chars = format.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '%' {
            let mut suppress = false;
            let mut width = None;

            // Check for %%
            if chars.peek() == Some(&'%') {
                chars.next();
                specs.push(FormatSpec {
                    suppress: false,
                    width: None,
                    conversion: ConversionSpec::Percent,
                });
                continue;
            }

            // Assignment suppression
            if chars.peek() == Some(&'*') {
                suppress = true;
                chars.next();
            }

            // Field width
            let mut width_str = String::new();
            while let Some(&digit) = chars.peek() {
                if digit.is_ascii_digit() {
                    width_str.push(digit);
                    chars.next();
                } else {
                    break;
                }
            }
            if !width_str.is_empty() {
                width = Some(width_str.parse().map_err(|_| ScanError::InvalidFormat)?);
            }

            // Length modifier
            let length_mod = match chars.peek() {
                Some(&'h') => {
                    chars.next();
                    if chars.peek() == Some(&'h') {
                        chars.next();
                        LengthModifier::Hh
                    } else {
                        LengthModifier::H
                    }
                }
                Some(&'l') => {
                    chars.next();
                    if chars.peek() == Some(&'l') {
                        chars.next();
                        LengthModifier::Ll
                    } else {
                        LengthModifier::L
                    }
                }
                Some(&'L') => {
                    chars.next();
                    LengthModifier::L
                }
                Some(&'j') => {
                    chars.next();
                    LengthModifier::J
                }
                Some(&'z') => {
                    chars.next();
                    LengthModifier::Z
                }
                Some(&'t') => {
                    chars.next();
                    LengthModifier::T
                }
                _ => LengthModifier::None,
            };

            // Conversion specifier
            let conversion = match chars.next() {
                Some('d') => ConversionSpec::SignedInt(length_mod),
                Some('i') => ConversionSpec::AutoInt(length_mod),
                Some('u') => ConversionSpec::UnsignedInt(length_mod),
                Some('o') => ConversionSpec::OctalInt(length_mod),
                Some('x') | Some('X') => ConversionSpec::HexInt(length_mod),
                Some('f') | Some('e') | Some('g') | Some('a') | Some('F') | Some('E')
                | Some('G') | Some('A') => ConversionSpec::Float(length_mod),
                Some('s') => ConversionSpec::String,
                Some('c') => ConversionSpec::Char(width.unwrap_or(1)),
                Some('n') => ConversionSpec::Position,
                Some('p') => ConversionSpec::Pointer,
                Some('[') => {
                    let inverted = chars.peek() == Some(&'^');
                    if inverted {
                        chars.next();
                    }

                    let mut charset = String::new();
                    let mut first = true;

                    while let Some(&ch) = chars.peek() {
                        chars.next();
                        if ch == ']' && !first {
                            break;
                        }
                        charset.push(ch);
                        first = false;
                    }

                    // Expand ranges
                    let expanded = expand_charset(&charset);
                    ConversionSpec::CharSet {
                        inverted,
                        chars: expanded,
                    }
                }
                _ => return Err(ScanError::InvalidFormat),
            };

            specs.push(FormatSpec {
                suppress,
                width,
                conversion,
            });
        } else if ch.is_whitespace() {
            // Whitespace in format matches any amount of whitespace
            specs.push(FormatSpec {
                suppress: false,
                width: None,
                conversion: ConversionSpec::Literal(' '),
            });
        } else {
            // Literal character
            specs.push(FormatSpec {
                suppress: false,
                width: None,
                conversion: ConversionSpec::Literal(ch),
            });
        }
    }

    Ok(specs)
}

/// Counts the number of assigned values (excludes Position values from `%n`).
fn count_assigned(values: &[ScanValue]) -> usize {
    values.iter().filter(|v| !matches!(v, ScanValue::Position(_))).count()
}

/// Expands character ranges in a character set specification.
///
/// For example, "a-z" becomes "abcdefghijklmnopqrstuvwxyz".
fn expand_charset(charset: &str) -> String {
    let mut result = String::new();
    let chars: Vec<char> = charset.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if i + 2 < chars.len() && chars[i + 1] == '-' {
            // Range
            let start = chars[i] as u8;
            let end = chars[i + 2] as u8;
            for ch in start..=end {
                result.push(ch as char);
            }
            i += 3;
        } else {
            result.push(chars[i]);
            i += 1;
        }
    }

    result
}

/// Parses an input string according to a format specification.
///
/// # Arguments
///
/// * `input` - The input string to parse.
/// * `format` - A scanf-style format string.
///
/// # Returns
///
/// On success, returns a vector of [`ScanValue`]s parsed from input.
/// This includes values from `%n` (position) conversions.
///
/// # Errors
///
/// - [`ScanError::Eof`] - Input exhausted before first conversion
/// - [`ScanError::MatchFailure`] - Input doesn't match format
/// - [`ScanError::InvalidFormat`] - Malformed format string
///
/// # Behavior Notes
///
/// - Whitespace in format matches any amount of input whitespace
/// - `%c` and `%[...]` do NOT skip leading whitespace (use explicit space in format)
/// - Partial matches return successfully with the values parsed so far
/// - `%n` stores position and is included in the returned vector
///
/// # Example
///
/// ```
/// use xj_scanf::{scanf_str, ScanValue};
///
/// // Parse multiple types
/// let values = scanf_str("42 3.14 hello", "%d %f %s").unwrap();
/// assert_eq!(values.len(), 3);
///
/// // Parse with position tracking
/// let values = scanf_str("abc", "%s%n").unwrap();
/// assert_eq!(values.len(), 2);
/// if let ScanValue::Position(pos) = values[1] {
///     assert_eq!(pos, 3);
/// }
///
/// // Assignment suppression
/// let values = scanf_str("1 2 3", "%*d %d %*d").unwrap();
/// assert_eq!(values.len(), 1); // Only middle value assigned
/// ```
pub fn scanf_str(input: &str, format: &str) -> ScanResult<Vec<ScanValue>> {
    scanf_core(input.as_bytes(), format)
}

/// Parses input from a [`BufRead`] source according to a format specification.
///
/// This is the generalized version of [`scanf_str`] that works with any buffered
/// reader, enabling scanf-style parsing from files, stdin, or other IO sources.
///
/// # Arguments
///
/// * `reader` - Any type implementing [`BufRead`] to read input from.
/// * `format` - A scanf-style format string.
///
/// # Returns
///
/// On success, returns a vector of [`ScanValue`]s parsed from input.
/// This includes values from `%n` (position) conversions.
///
/// # Errors
///
/// - [`ScanError::Eof`] - Input exhausted before first conversion
/// - [`ScanError::MatchFailure`] - Input doesn't match format
/// - [`ScanError::InvalidFormat`] - Malformed format string
///
/// # Example
///
/// ```
/// use xj_scanf::{scanf_core, ScanValue};
/// use std::io::Cursor;
///
/// let data = Cursor::new("123 456");
/// let values = scanf_core(data, "%d %d").unwrap();
/// assert_eq!(values.len(), 2);
/// ```
pub fn scanf_core<R: BufRead>(reader: R, format: &str) -> ScanResult<Vec<ScanValue>> {
    let specs = parse_format(format)?;
    let mut parser = Parser::new(reader);
    let mut values = Vec::new();

    if parser.peek().is_none() && !specs.is_empty() {
        // Check if first spec would require input
        match &specs[0].conversion {
            ConversionSpec::Percent | ConversionSpec::Literal(_) => {}
            _ => return Err(ScanError::Eof),
        }
    }

    for spec in specs {
        match spec.conversion {
            ConversionSpec::SignedInt(len_mod) => {
                parser.skip_whitespace();
                match parser.read_int(spec.width, 10, true) {
                    Ok(s) => {
                        if !spec.suppress {
                            let val = s.parse::<i64>().map_err(|_| ScanError::MatchFailure)?;
                            values.push(match len_mod {
                                LengthModifier::None => ScanValue::I32(val as i32),
                                _ => ScanValue::I64(val),
                            });
                        }
                    }
                    Err(e) => {
                        if count_assigned(&values) == 0 {
                            return Err(e);
                        }
                        break;
                    }
                }
            }
            ConversionSpec::UnsignedInt(len_mod) => {
                parser.skip_whitespace();
                match parser.read_int(spec.width, 10, false) {
                    Ok(s) => {
                        if !spec.suppress {
                            let val = s.parse::<u64>().map_err(|_| ScanError::MatchFailure)?;
                            values.push(match len_mod {
                                LengthModifier::None => ScanValue::U32(val as u32),
                                _ => ScanValue::U64(val),
                            });
                        }
                    }
                    Err(e) => {
                        if count_assigned(&values) == 0 {
                            return Err(e);
                        }
                        break;
                    }
                }
            }
            ConversionSpec::OctalInt(len_mod) => {
                parser.skip_whitespace();
                match parser.read_int(spec.width, 8, false) {
                    Ok(s) => {
                        if !spec.suppress {
                            let val =
                                u64::from_str_radix(&s, 8).map_err(|_| ScanError::MatchFailure)?;
                            values.push(match len_mod {
                                LengthModifier::None => ScanValue::U32(val as u32),
                                _ => ScanValue::U64(val),
                            });
                        }
                    }
                    Err(e) => {
                        if count_assigned(&values) == 0 {
                            return Err(e);
                        }
                        break;
                    }
                }
            }
            ConversionSpec::HexInt(len_mod) => {
                parser.skip_whitespace();
                match parser.read_int(spec.width, 16, false) {
                    Ok(s) => {
                        if !spec.suppress {
                            // Strip 0x/0X prefix if present
                            let hex_str = if s.starts_with("0x") || s.starts_with("0X") {
                                &s[2..]
                            } else {
                                &s
                            };
                            let val = u64::from_str_radix(hex_str, 16)
                                .map_err(|_| ScanError::MatchFailure)?;
                            values.push(match len_mod {
                                LengthModifier::None => ScanValue::U32(val as u32),
                                _ => ScanValue::U64(val),
                            });
                        }
                    }
                    Err(e) => {
                        if count_assigned(&values) == 0 {
                            return Err(e);
                        }
                        break;
                    }
                }
            }
            ConversionSpec::AutoInt(len_mod) => {
                parser.skip_whitespace();
                match parser.read_auto_int(spec.width, true) {
                    Ok((s, base)) => {
                        if !spec.suppress {
                            // Strip 0x/0X prefix if present for hex
                            let int_str =
                                if base == 16 && (s.starts_with("0x") || s.starts_with("0X")) {
                                    &s[2..]
                                } else {
                                    &s
                                };
                            let val = i64::from_str_radix(int_str, base)
                                .map_err(|_| ScanError::MatchFailure)?;
                            values.push(match len_mod {
                                LengthModifier::None => ScanValue::I32(val as i32),
                                _ => ScanValue::I64(val),
                            });
                        }
                    }
                    Err(e) => {
                        if count_assigned(&values) == 0 {
                            return Err(e);
                        }
                        break;
                    }
                }
            }
            ConversionSpec::Float(len_mod) => {
                parser.skip_whitespace();
                match parser.read_float(spec.width) {
                    Ok(s) => {
                        if !spec.suppress {
                            match len_mod {
                                LengthModifier::L => {
                                    let val =
                                        s.parse::<f64>().map_err(|_| ScanError::MatchFailure)?;
                                    values.push(ScanValue::F64(val));
                                }
                                _ => {
                                    let val =
                                        s.parse::<f32>().map_err(|_| ScanError::MatchFailure)?;
                                    values.push(ScanValue::F32(val));
                                }
                            }
                        }
                    }
                    Err(e) => {
                        if count_assigned(&values) == 0 {
                            return Err(e);
                        }
                        break;
                    }
                }
            }
            ConversionSpec::String => {
                parser.skip_whitespace();
                match parser.read_string(spec.width) {
                    Ok(s) => {
                        if !spec.suppress {
                            values.push(ScanValue::String(s));
                        }
                    }
                    Err(e) => {
                        if count_assigned(&values) == 0 && e == ScanError::Eof {
                            return Err(ScanError::Eof);
                        }
                        return Err(e);
                    }
                }
            }
            ConversionSpec::Char(count) => match parser.read_chars(count) {
                Ok(chars) => {
                    if !spec.suppress {
                        if count == 1 {
                            values.push(ScanValue::Char(chars[0] as char));
                        } else {
                            values.push(ScanValue::Chars(chars));
                        }
                    }
                }
                Err(e) => {
                    if count_assigned(&values) == 0 {
                        return Err(e);
                    }
                    break;
                }
            },
            ConversionSpec::CharSet {
                inverted,
                ref chars,
            } => match parser.read_charset(inverted, chars, spec.width) {
                Ok(s) => {
                    if !spec.suppress {
                        values.push(ScanValue::String(s));
                    }
                }
                Err(e) => {
                    if count_assigned(&values) == 0 {
                        return Err(e);
                    }
                    break;
                }
            },
            ConversionSpec::Position => {
                if !spec.suppress {
                    values.push(ScanValue::Position(parser.pos));
                }
            }
            ConversionSpec::Literal(ch) => {
                if ch.is_whitespace() {
                    parser.skip_whitespace();
                } else {
                    match parser.consume() {
                        Some(input_ch) if input_ch == ch as u8 => {} // Match
                        Some(other_ch) => {
                            // Mismatch - put byte back
                            parser.unconsume(other_ch);
                            if count_assigned(&values) == 0 {
                                return Err(ScanError::MatchFailure);
                            }
                            break;
                        }
                        None => {
                            // EOF
                            if count_assigned(&values) == 0 {
                                return Err(ScanError::Eof);
                            }
                            break;
                        }
                    }
                }
            }
            ConversionSpec::Percent => match parser.consume() {
                Some(b'%') => {}
                _ => {
                    if count_assigned(&values) == 0 {
                        return Err(ScanError::MatchFailure);
                    }
                    break;
                }
            },
            ConversionSpec::Pointer => {
                return Err(ScanError::InvalidFormat);
            }
        }
    }

    Ok(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_decimal_int() {
        let values = scanf_str("42", "%d").unwrap();
        assert_eq!(values.len(), 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 42),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_negative_int() {
        let values = scanf_str("-123", "%d").unwrap();
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, -123),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_multiple_ints() {
        let values = scanf_str("1 2 3", "%d %d %d").unwrap();
        match (&values[0], &values[1], &values[2]) {
            (ScanValue::I32(a), ScanValue::I32(b), ScanValue::I32(c)) => {
                assert_eq!(*a, 1);
                assert_eq!(*b, 2);
                assert_eq!(*c, 3);
            }
            _ => panic!("Wrong types"),
        }
    }

    #[test]
    fn test_unsigned_int() {
        let values = scanf_str("4294967295", "%u").unwrap();
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 4294967295),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_octal_int() {
        let values = scanf_str("755", "%o").unwrap();
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 0o755),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_hex_int() {
        let values = scanf_str("1a2b", "%x").unwrap();
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 0x1a2b),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_hex_with_prefix() {
        let values = scanf_str("0xDEAD", "%x").unwrap();
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 0xDEAD),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_i_decimal() {
        let values = scanf_str("123", "%i").unwrap();
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 123),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_i_octal() {
        let values = scanf_str("0755", "%i").unwrap();
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 0o755),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_i_hex() {
        let values = scanf_str("0x1A", "%i").unwrap();
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 0x1A),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_float_basic() {
        let values = scanf_str("3.14", "%f").unwrap();
        match values[0] {
            ScanValue::F32(x) => assert!((x - 3.14).abs() < 0.001),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_float_negative() {
        let values = scanf_str("-2.5", "%f").unwrap();
        match values[0] {
            ScanValue::F32(x) => assert!((x + 2.5).abs() < 0.001),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_float_exponent() {
        let values = scanf_str("1.5e2", "%f").unwrap();
        match values[0] {
            ScanValue::F32(x) => assert!((x - 150.0).abs() < 0.001),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_string_basic() {
        let values = scanf_str("hello", "%s").unwrap();
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "hello"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_string_stops_at_whitespace() {
        let values = scanf_str("hello world", "%s").unwrap();
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "hello"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_string_with_width() {
        let values = scanf_str("verylongword", "%5s").unwrap();
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "veryl"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_multiple_strings() {
        let values = scanf_str("hello world", "%s %s").unwrap();
        match (&values[0], &values[1]) {
            (ScanValue::String(s1), ScanValue::String(s2)) => {
                assert_eq!(s1, "hello");
                assert_eq!(s2, "world");
            }
            _ => panic!("Wrong types"),
        }
    }

    #[test]
    fn test_char_single() {
        let values = scanf_str("A", "%c").unwrap();
        match values[0] {
            ScanValue::Char(c) => assert_eq!(c, 'A'),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_char_no_whitespace_skip() {
        let values = scanf_str(" A", "%c").unwrap();
        match values[0] {
            ScanValue::Char(c) => assert_eq!(c, ' '),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_char_multiple() {
        let values = scanf_str("ABCD", "%3c").unwrap();
        match &values[0] {
            ScanValue::Chars(chars) => {
                assert_eq!(chars.len(), 3);
                assert_eq!(chars[0], b'A');
                assert_eq!(chars[1], b'B');
                assert_eq!(chars[2], b'C');
            }
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_charset_basic() {
        let values = scanf_str("abc123", "%[a-z]").unwrap();
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "abc"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_charset_inverted() {
        let values = scanf_str("abc:def", "%[^:]").unwrap();
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "abc"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_suppression_int() {
        let values = scanf_str("1 2 3", "%*d %d %*d").unwrap();
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 2),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_n_at_end() {
        let values = scanf_str("123", "%d%n").unwrap();
        match (&values[0], &values[1]) {
            (ScanValue::I32(x), ScanValue::Position(n)) => {
                assert_eq!(*x, 123);
                assert_eq!(*n, 3);
            }
            _ => panic!("Wrong types"),
        }
    }

    #[test]
    fn test_literal_match() {
        let values = scanf_str("1,2", "%d,%d").unwrap();
        match (&values[0], &values[1]) {
            (ScanValue::I32(x), ScanValue::I32(y)) => {
                assert_eq!(*x, 1);
                assert_eq!(*y, 2);
            }
            _ => panic!("Wrong types"),
        }
    }

    #[test]
    fn test_empty_input() {
        let result = scanf_str("", "%d");
        assert_eq!(result, Err(ScanError::Eof));
    }

    #[test]
    fn test_matching_failure() {
        let result = scanf_str("abc", "%d");
        assert_eq!(result, Err(ScanError::MatchFailure));
    }

    #[test]
    fn test_partial_match() {
        let values = scanf_str("123 abc", "%d %d").unwrap();
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 123),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_percent_literal() {
        let values = scanf_str("%42", "%%%d").unwrap();
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 42),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_eof_in_format() {
        let values = scanf_str("0", "%f%c").unwrap();
        assert_eq!(values.len(), 1);
        match values[0] {
            ScanValue::F32(f) => assert_eq!(f, 0.0f32),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_literal_eof() {
        let result = scanf_str("", "a");
        assert_eq!(result, Err(ScanError::Eof));
    }

    #[test]
    fn test_space_multi_char() {
        let result = scanf_str(" xxx", "%3c");
        assert_eq!(result, Ok(vec![ScanValue::Chars(" xx".into())]));
    }

    #[test]
    fn test_space_string() {
        let result = scanf_str(" xxx", "%3s");
        assert_eq!(result, Ok(vec![ScanValue::String("xxx".into())]));
    }

    #[test]
    fn test_bytes_consumed_at_eof() {
        let values = scanf_str("aa", "%s%n").unwrap();
        assert_eq!(values.len(), 2);
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "aa"),
            _ => panic!("Wrong type for value 0"),
        }
        match &values[1] {
            ScanValue::Position(p) => assert_eq!(*p, 2),
            _ => panic!("Wrong type for value 1"),
        }
    }

    #[test]
    fn test_nontrivial_1() {
        let input = "4
-2-2.0211.968
0
0
0
07
2.0.0
8
86";
        let result = scanf_str(input, "%d%f%f%f%d%d%d%d%f%f%f%d");
        use crate::ScanValue::*;
        assert_eq!(result,
            Ok(vec![I32(4), F32(-2.0), F32(-2.0211), F32(0.968),
                    I32(0), I32(0), I32(0), I32(7), F32(2.0),
                    F32(0.0), F32(8.0), I32(86)]));
    }
}
