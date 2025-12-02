//! Legacy C-compatible API for sscanf.
//!
//! This module provides a C-style interface using mutable references instead of
//! pointers, with return values matching C's sscanf semantics (count or EOF).
//!
//! # Example
//!
//! ```
//! use xj_scanf::legacy::{sscanf, ScanTarget};
//!
//! let mut x: i32 = 0;
//! let mut y: f32 = 0.0;
//! let mut s = String::new();
//!
//! let count = sscanf("42 3.14 hello", "%d %f %s", &mut [&mut x, &mut y, &mut s]);
//! assert_eq!(count, 3);
//! assert_eq!(x, 42);
//! assert!((y - 3.14).abs() < 0.01);
//! assert_eq!(s, "hello");
//! ```
//!
//! # Using the macro
//!
//! ```
//! use xj_scanf::{sscanf, legacy::ScanTarget};
//!
//! let mut a: i32 = 0;
//! let mut b: i32 = 0;
//! let count = sscanf!("1 2", "%d %d", &mut a, &mut b);
//! assert_eq!(count, 2);
//! ```

use crate::{scanf_core, scanf_str, ScanError, ScanResult, ScanValue};
use std::io::{BufRead, stdin};

/// Trait for types that can receive scanned values.
///
/// Implement this trait for custom types that should be usable as fscanf/sscanf targets.
pub trait ScanTarget {
    /// Store a scanned value into this target.
    ///
    /// Returns `true` if the value was successfully stored (type matched),
    /// `false` otherwise.
    fn store(&mut self, value: &ScanValue) -> bool;
}

impl ScanTarget for i32 {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::I32(v) => {
                *self = *v;
                true
            }
            ScanValue::I64(v) => {
                *self = *v as i32;
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for i64 {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::I32(v) => {
                *self = *v as i64;
                true
            }
            ScanValue::I64(v) => {
                *self = *v;
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for u32 {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::U32(v) => {
                *self = *v;
                true
            }
            ScanValue::U64(v) => {
                *self = *v as u32;
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for u64 {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::U32(v) => {
                *self = *v as u64;
                true
            }
            ScanValue::U64(v) => {
                *self = *v;
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for f32 {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::F32(v) => {
                *self = *v;
                true
            }
            ScanValue::F64(v) => {
                *self = *v as f32;
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for f64 {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::F32(v) => {
                *self = *v as f64;
                true
            }
            ScanValue::F64(v) => {
                *self = *v;
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for char {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::Char(v) => {
                *self = *v;
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for String {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::String(v) => {
                *self = v.clone();
                true
            }
            ScanValue::Char(v) => {
                self.clear();
                self.push(*v);
                true
            }
            ScanValue::Chars(v) => {
                *self = String::from_utf8_lossy(v).into_owned();
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for Vec<u8> {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::Chars(v) => {
                *self = v.clone();
                true
            }
            ScanValue::Char(v) => {
                self.clear();
                self.push(*v as u8);
                true
            }
            ScanValue::String(v) => {
                *self = v.as_bytes().to_vec();
                true
            }
            _ => false,
        }
    }
}

impl ScanTarget for usize {
    fn store(&mut self, value: &ScanValue) -> bool {
        match value {
            ScanValue::Position(v) => {
                *self = *v;
                true
            }
            ScanValue::U32(v) => {
                *self = *v as usize;
                true
            }
            ScanValue::U64(v) => {
                *self = *v as usize;
                true
            }
            _ => false,
        }
    }
}

/// Helper to convert scanf result to C-style return value and store values.
fn process_scanf_result(
    result: ScanResult<Vec<ScanValue>>,
    args: &mut [&mut dyn ScanTarget],
) -> i32 {
    match result {
        Ok(values) => {
            // Count non-Position values (Position from %n doesn't count toward assignment count)
            let count = values.iter()
                .filter(|v| !matches!(v, ScanValue::Position(_)))
                .count();

            for (arg, val) in args.iter_mut().zip(values.iter()) {
                arg.store(val);
            }
            count as i32
        }
        Err(ScanError::Eof) => -1,
        Err(ScanError::MatchFailure) => 0,
        Err(ScanError::InvalidFormat) => -1,
    }
}

/// C-compatible sscanf function.
///
/// Parses the input string according to the format specification and stores
/// the results in the provided mutable references.
///
/// # Arguments
///
/// * `input` - The input string to parse.
/// * `format` - A scanf-style format string.
/// * `args` - Mutable references to store the parsed values.
///
/// # Returns
///
/// * Positive integer: Number of successfully assigned conversions
/// * `0`: Input available but first conversion failed
/// * `-1`: EOF (input exhausted before any conversion)
///
/// # Example
///
/// ```
/// use xj_scanf::legacy::{sscanf, ScanTarget};
///
/// let mut x: i32 = 0;
/// let mut y: i32 = 0;
/// let count = sscanf("10 20", "%d %d", &mut [&mut x, &mut y]);
/// assert_eq!(count, 2);
/// assert_eq!(x, 10);
/// assert_eq!(y, 20);
/// ```
pub fn sscanf(input: &str, format: &str, args: &mut [&mut dyn ScanTarget]) -> i32 {
    process_scanf_result(scanf_str(input, format), args)
}

/// C-compatible scanf function that reads from a BufRead source.
///
/// Parses input from any buffered reader according to the format specification
/// and stores the results in the provided mutable references.
///
/// # Arguments
///
/// * `reader` - Any type implementing [`BufRead`] to read input from.
/// * `format` - A scanf-style format string.
/// * `args` - Mutable references to store the parsed values.
///
/// # Returns
///
/// * Positive integer: Number of successfully assigned conversions
/// * `0`: Input available but first conversion failed
/// * `-1`: EOF (input exhausted before any conversion)
///
/// # Example
///
/// ```
/// use xj_scanf::legacy::{brscanf, ScanTarget};
/// use std::io::Cursor;
///
/// let input = Cursor::new("42 3.14");
/// let mut x: i32 = 0;
/// let mut y: f32 = 0.0;
/// let count = brscanf(input, "%d %f", &mut [&mut x, &mut y]);
/// assert_eq!(count, 2);
/// assert_eq!(x, 42);
/// ```
pub fn brscanf<R: BufRead>(reader: R, format: &str, args: &mut [&mut dyn ScanTarget]) -> i32 {
    process_scanf_result(scanf_core(reader, format), args)
}

/// C-compatible scanf function that reads from standard input.
///
/// Parses input from stdin according to the format specification and stores
/// the results in the provided mutable references.
///
/// # Arguments
///
/// * `format` - A scanf-style format string.
/// * `args` - Mutable references to store the parsed values.
///
/// # Returns
///
/// * Positive integer: Number of successfully assigned conversions
/// * `0`: Input available but first conversion failed
/// * `-1`: EOF (input exhausted before any conversion)
///
/// # Example
///
/// ```no_run
/// use xj_scanf::legacy::{scanf, ScanTarget};
///
/// let mut x: i32 = 0;
/// let mut y: i32 = 0;
/// let count = scanf("%d %d", &mut [&mut x, &mut y]);
/// ```
pub fn scanf(format: &str, args: &mut [&mut dyn ScanTarget]) -> i32 {
    process_scanf_result(scanf_core(stdin().lock(), format), args)
}

/// Macro for C-style sscanf with variadic arguments.
///
/// This macro provides a more ergonomic interface that resembles C's sscanf.
///
/// # Example
///
/// ```
/// use xj_scanf::{sscanf, legacy::ScanTarget};
///
/// let mut x: i32 = 0;
/// let mut name = String::new();
/// let count = sscanf!("42 Alice", "%d %s", &mut x, &mut name);
/// assert_eq!(count, 2);
/// assert_eq!(x, 42);
/// assert_eq!(name, "Alice");
/// ```
#[macro_export]
macro_rules! sscanf {
    ($input:expr, $fmt:expr $(,)?) => {{
        $crate::legacy::sscanf($input, $fmt, &mut [])
    }};
    ($input:expr, $fmt:expr, $($arg:expr),+ $(,)?) => {{
        $crate::legacy::sscanf($input, $fmt, &mut [$($arg as &mut dyn $crate::legacy::ScanTarget),+])
    }};
}

/// Macro for C-style scanf with variadic arguments reading from stdin.
///
/// This macro provides a more ergonomic interface that resembles C's scanf.
///
/// # Example
///
/// ```no_run
/// use xj_scanf::{scanf, legacy::ScanTarget};
///
/// let mut x: i32 = 0;
/// let mut y: i32 = 0;
/// let count = scanf!("%d %d", &mut x, &mut y);
/// ```
#[macro_export]
macro_rules! scanf {
    ($fmt:expr $(,)?) => {{
        $crate::legacy::scanf($fmt, &mut [])
    }};
    ($fmt:expr, $($arg:expr),+ $(,)?) => {{
        $crate::legacy::scanf($fmt, &mut [$($arg as &mut dyn $crate::legacy::ScanTarget),+])
    }};
}

/// Macro for C-style scanf with variadic arguments reading from a BufRead source.
///
/// This macro provides a more ergonomic interface for reading from any buffered reader.
///
/// # Example
///
/// ```
/// use xj_scanf::{brscanf, legacy::ScanTarget};
/// use std::io::Cursor;
///
/// let input = Cursor::new("42 3.14");
/// let mut x: i32 = 0;
/// let mut y: f32 = 0.0;
/// let count = brscanf!(input, "%d %f", &mut x, &mut y);
/// assert_eq!(count, 2);
/// assert_eq!(x, 42);
/// ```
#[macro_export]
macro_rules! brscanf {
    ($reader:expr, $fmt:expr $(,)?) => {{
        $crate::legacy::brscanf($reader, $fmt, &mut [])
    }};
    ($reader:expr, $fmt:expr, $($arg:expr),+ $(,)?) => {{
        $crate::legacy::brscanf($reader, $fmt, &mut [$($arg as &mut dyn $crate::legacy::ScanTarget),+])
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanf_single_int() {
        let mut x: i32 = 0;
        let count = sscanf("42", "%d", &mut [&mut x]);
        assert_eq!(count, 1);
        assert_eq!(x, 42);
    }

    #[test]
    fn test_scanf_multiple_ints() {
        let mut a: i32 = 0;
        let mut b: i32 = 0;
        let mut c: i32 = 0;
        let count = sscanf("1 2 3", "%d %d %d", &mut [&mut a, &mut b, &mut c]);
        assert_eq!(count, 3);
        assert_eq!(a, 1);
        assert_eq!(b, 2);
        assert_eq!(c, 3);
    }

    #[test]
    fn test_scanf_mixed_types() {
        let mut i: i32 = 0;
        let mut f: f32 = 0.0;
        let mut s = String::new();
        let count = sscanf("42 3.14 hello", "%d %f %s", &mut [&mut i, &mut f, &mut s]);
        assert_eq!(count, 3);
        assert_eq!(i, 42);
        assert!((f - 3.14).abs() < 0.01);
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_scanf_eof() {
        let mut x: i32 = 0;
        let count = sscanf("", "%d", &mut [&mut x]);
        assert_eq!(count, -1);
    }

    #[test]
    fn test_scanf_match_failure() {
        let mut x: i32 = 0;
        let count = sscanf("abc", "%d", &mut [&mut x]);
        assert_eq!(count, 0);
    }

    #[test]
    fn test_scanf_partial_match() {
        let mut a: i32 = 0;
        let mut b: i32 = 0;
        let count = sscanf("42 abc", "%d %d", &mut [&mut a, &mut b]);
        assert_eq!(count, 1);
        assert_eq!(a, 42);
    }

    #[test]
    fn test_scanf_char() {
        let mut c: char = '\0';
        let count = sscanf("X", "%c", &mut [&mut c]);
        assert_eq!(count, 1);
        assert_eq!(c, 'X');
    }

    #[test]
    fn test_scanf_position() {
        let mut x: i32 = 0;
        let mut pos: usize = 0;
        let count = sscanf("123", "%d%n", &mut [&mut x, &mut pos]);
        assert_eq!(count, 1);
        assert_eq!(x, 123);
        assert_eq!(pos, 3);
    }

    #[test]
    fn test_scanf_unsigned() {
        let mut u: u32 = 0;
        let count = sscanf("4294967295", "%u", &mut [&mut u]);
        assert_eq!(count, 1);
        assert_eq!(u, 4294967295);
    }

    #[test]
    fn test_scanf_hex() {
        let mut x: u32 = 0;
        let count = sscanf("0xFF", "%x", &mut [&mut x]);
        assert_eq!(count, 1);
        assert_eq!(x, 255);
    }

    #[test]
    fn test_scanf_macro_single() {
        let mut x: i32 = 0;
        let count = sscanf!("42", "%d", &mut x);
        assert_eq!(count, 1);
        assert_eq!(x, 42);
    }

    #[test]
    fn test_scanf_macro_multiple() {
        let mut a: i32 = 0;
        let mut b: f32 = 0.0;
        let count = sscanf!("10 2.5", "%d %f", &mut a, &mut b);
        assert_eq!(count, 2);
        assert_eq!(a, 10);
        assert!((b - 2.5).abs() < 0.01);
    }

    #[test]
    fn test_scanf_macro_no_args() {
        let count = sscanf!("%%", "%%%%");
        assert_eq!(count, 0);
    }

    #[test]
    fn test_scanf_i64() {
        let mut x: i64 = 0;
        let count = sscanf("9223372036854775807", "%ld", &mut [&mut x]);
        assert_eq!(count, 1);
        assert_eq!(x, 9223372036854775807i64);
    }

    #[test]
    fn test_scanf_vec_u8() {
        let mut buf: Vec<u8> = Vec::new();
        let count = sscanf("ABC", "%3c", &mut [&mut buf]);
        assert_eq!(count, 1);
        assert_eq!(buf, vec![b'A', b'B', b'C']);
    }

    #[test]
    fn test_brscanf_macro_single() {
        use std::io::Cursor;
        let input = Cursor::new("42");
        let mut x: i32 = 0;
        let count = brscanf!(input, "%d", &mut x);
        assert_eq!(count, 1);
        assert_eq!(x, 42);
    }

    #[test]
    fn test_brscanf_macro_multiple() {
        use std::io::Cursor;
        let input = Cursor::new("10 2.5 hello");
        let mut a: i32 = 0;
        let mut b: f32 = 0.0;
        let mut s = String::new();
        let count = brscanf!(input, "%d %f %s", &mut a, &mut b, &mut s);
        assert_eq!(count, 3);
        assert_eq!(a, 10);
        assert!((b - 2.5).abs() < 0.01);
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_brscanf_macro_no_args() {
        use std::io::Cursor;
        let input = Cursor::new("%%");
        let count = brscanf!(input, "%%%%");
        assert_eq!(count, 0);
    }
}
