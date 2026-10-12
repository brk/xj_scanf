//! A safe Rust implementation of C's `scanf` family.
//!
//! One engine ([`vscan`]) serves every front end: in-memory C strings
//! ([`sscanf`], [`bscanf`]), buffered readers ([`brscanf`]), and the stream
//! functions of `xj_cio`. The format grammar and destination requirements
//! live in [`xj_scanf_core`], which this crate re-exports.
//!
//! ```
//! use xj_scanf::sscanf;
//!
//! let mut n: i32 = 0;
//! let mut x: f32 = 0.0;
//! let mut word = [0u8; 8];
//! let count = sscanf("42 3.5 hello", "%d %f %7s", &mut [&mut n, &mut x, &mut word]);
//! assert_eq!((count, n, x), (3, 42, 3.5));
//! assert_eq!(&word, b"hello\0\0\0");
//! ```
//!
//! # Semantics
//!
//! - **The C standard** (C11 §7.21.6.2) decides behavior where glibc
//!   differs, in the C locale. Input items are the longest prefix of a
//!   matching sequence, so `"0xg"` with `%x` and `"100er"` with `%f` are
//!   matching failures that leave `g` and `r` unread.
//! - **Bytes, not text.** Inputs and formats are [`ByteView`]s. In-memory
//!   inputs and all formats stop at the first NUL or view end. Fields are
//!   stored byte for byte, without re-encoding.
//! - **Destinations** are claimed in order and checked against each
//!   directive before it reads input. Signedness differences and
//!   equal-width integer types are accepted; width and class differences
//!   stop the scan with [`StoreError::TypeMismatch`]. `%n` stores into any
//!   integer of its width.
//! - **Integer overflow** saturates silently to the destination's range.
//!   Negative input to an unsigned destination is converted modulo its range
//!   when the magnitude fits (`-1` stores the maximum). An unsigned
//!   directive's in-range value keeps its bit pattern in a signed
//!   destination of the same width (`%hhu` with 255 stores -1 in an `i8`).
//! - **Bounded byte destinations** (`[u8; N]`, `&mut [u8]`,
//!   [`CStrDest`](xj_bytes::CStrDest)) never overflow. A `%s` or `%[` field
//!   that does not fit stores the prefix that fits, terminated, leaves the
//!   rest unread and stops with [`StoreError::Capacity`]. `Vec<u8>` and
//!   `String` grow instead.
//! - **Unsupported directives** (`%p`, `L`, wide conversions) are format
//!   errors, detected before any input is read.
//!
//! # Return values
//!
//! The C-style front ends return the number of assignments, or `-1` (EOF)
//! when input ends or fails before the first input conversion completes.
//! [`vscan`] returns the structured [`ScanOutcome`].

mod engine;
mod float;
mod target;

use std::io::{self, BufRead};

pub use engine::vscan;
pub use target::{ScanTarget, Targets, int_bits, signed_value, unsigned_value};
/// Shared borrowed byte inputs for in-memory data and scanf formats.
pub use xj_bytes::ByteView;
use xj_bytes::c_bytes;
/// The format grammar and destination requirements.
pub use xj_scanf_core;
pub use xj_scanf_core::{Conv, Directive, FormatError, IntKind, LengthMod, Requirement};

/// Input with one byte of lookahead.
///
/// Peeking replaces pushback: the engine never takes a byte it cannot
/// return, so a byte that ends an item stays in the input.
pub trait ScanInput {
    /// The next byte without consuming it. `Ok(None)` is end of input; an
    /// I/O error is reported separately.
    fn peek(&mut self) -> io::Result<Option<u8>>;

    /// Consumes the byte returned by the last successful `peek`.
    fn bump(&mut self);

    /// The last `n` consumed bytes, for inputs that keep them in memory.
    /// Field bytes are then borrowed from the input instead of copied.
    fn recent(&self, n: usize) -> Option<&[u8]> {
        let _ = n;
        None
    }
}

/// In-memory input: every byte of the slice, including NULs.
pub struct SliceInput<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> SliceInput<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        SliceInput { bytes, pos: 0 }
    }

    /// The bytes not yet consumed.
    pub fn rest(&self) -> &'a [u8] {
        &self.bytes[self.pos..]
    }
}

impl ScanInput for SliceInput<'_> {
    fn peek(&mut self) -> io::Result<Option<u8>> {
        Ok(self.bytes.get(self.pos).copied())
    }

    fn bump(&mut self) {
        self.pos += 1;
    }

    fn recent(&self, n: usize) -> Option<&[u8]> {
        self.bytes.get(self.pos - n..self.pos)
    }
}

/// Input from a borrowed [`BufRead`]. A byte that ends an item stays in the
/// reader, so repeated calls on the same reader see consistent data.
pub struct ReadInput<R>(pub R);

impl<R: BufRead> ScanInput for ReadInput<R> {
    fn peek(&mut self) -> io::Result<Option<u8>> {
        loop {
            match self.0.fill_buf() {
                Ok(buf) => return Ok(buf.first().copied()),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            }
        }
    }

    fn bump(&mut self) {
        self.0.consume(1);
    }
}

/// Destinations, claimed in order by non-suppressed conversions.
pub trait ScanArgs {
    /// Claims the destination for the next non-suppressed conversion and
    /// validates its presence, type and bounds against `d`, before this
    /// directive skips whitespace or consumes field bytes. Each destination
    /// is claimed once, in order. Suppressed conversions claim none.
    ///
    /// Returns the destination's byte limit for this directive: `max_len()`
    /// for `%s`/`%[` (room is kept for the terminator), `region_len()` for
    /// `%c` (no terminator). `None` means unbounded storage or a non-byte
    /// destination.
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError>;

    /// Stores one conversion into the destination most recently claimed by
    /// `prepare`, as soon as it succeeds. An error stops the scan without
    /// counting this assignment.
    fn store(&mut self, d: &Directive, value: Value<'_>) -> Result<(), StoreError>;
}

/// A completed conversion.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value<'a> {
    /// An integer as sign and magnitude. `overflow` is set when the
    /// magnitude exceeded `u64`; `mag` is then `u64::MAX`.
    Int {
        neg: bool,
        mag: u64,
        overflow: bool,
    },
    Float32(f32),
    Float64(f64),
    /// A `%s`, `%[` or `%c` field.
    Bytes(&'a [u8]),
    /// `%n`: the bytes consumed so far in this call.
    Count(usize),
}

/// Why a destination could not be claimed or stored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreError {
    /// The destination's class or width does not fit the directive.
    TypeMismatch,
    /// A bounded byte destination is too small for the field.
    Capacity,
    /// Too few destinations.
    Missing,
}

/// The result of one scan.
#[derive(Debug)]
pub struct ScanOutcome {
    /// Assignments made, excluding `%n` and suppressed conversions.
    pub assigned: usize,
    /// An input conversion completed, including suppressed ones.
    pub any_input: bool,
    /// Bytes consumed in this call.
    pub consumed: usize,
    pub stop: Stop,
}

/// Why a scan stopped.
#[derive(Debug)]
pub enum Stop {
    FormatEnd,
    MatchingFailure,
    /// End of input during a directive.
    InputEnd,
    Io(io::Error),
    /// An invalid or unsupported directive at this format offset. The
    /// format is checked before any input is read.
    InvalidFormat {
        offset: usize,
    },
    /// `index` is the ordinal of the destination claimed (or being claimed).
    Store {
        index: usize,
        err: StoreError,
    },
}

impl ScanOutcome {
    /// C's return value: `-1` (EOF) if input ended or failed before the
    /// first input conversion completed, and otherwise the number of
    /// assignments.
    pub fn c_return(&self) -> core::ffi::c_int {
        match self.stop {
            Stop::InputEnd | Stop::Io(_) if !self.any_input => -1,
            _ => self.assigned.try_into().unwrap_or(core::ffi::c_int::MAX),
        }
    }
}

/// C `sscanf`: scans a C string, through its first NUL or view end.
///
/// ```
/// use xj_scanf::sscanf;
///
/// let (mut x, mut y) = (0i32, 0u32);
/// assert_eq!(sscanf("10 -1", "%d %u", &mut [&mut x, &mut y]), 2);
/// assert_eq!((x, y), (10, u32::MAX));
/// assert_eq!(sscanf("", "%d", &mut [&mut x]), -1);
/// ```
pub fn sscanf<I: ByteView + ?Sized, F: ByteView + ?Sized>(
    input: &I,
    format: &F,
    args: &mut [&mut dyn ScanTarget],
) -> core::ffi::c_int {
    let mut input = SliceInput::new(c_bytes(input.view_bytes()));
    vscan(&mut input, format.view_bytes(), &mut Targets::new(args)).c_return()
}

/// Alias of [`sscanf`] for borrowed byte inputs, with the same NUL handling.
///
/// To scan a complete slice in which NULs are ordinary input bytes, pass it
/// to [`brscanf`]: `&[u8]` implements [`BufRead`].
pub fn bscanf<I: ByteView + ?Sized, F: ByteView + ?Sized>(
    input: &I,
    format: &F,
    args: &mut [&mut dyn ScanTarget],
) -> core::ffi::c_int {
    sscanf(input, format, args)
}

/// Scans a [`BufRead`]. Pass `&mut reader` to keep using the reader: bytes
/// that end an item remain unread in it.
///
/// ```
/// use xj_scanf::brscanf;
///
/// let mut input: &[u8] = b"42\0rest";
/// let mut x = 0i32;
/// let mut rest = Vec::new();
/// assert_eq!(brscanf(&mut input, "%d%c", &mut [&mut x, &mut rest]), 2);
/// assert_eq!((x, &rest[..], input), (42, &b"\0"[..], &b"rest"[..]));
/// ```
pub fn brscanf<R: BufRead, F: ByteView + ?Sized>(
    reader: R,
    format: &F,
    args: &mut [&mut dyn ScanTarget],
) -> core::ffi::c_int {
    vscan(
        &mut ReadInput(reader),
        format.view_bytes(),
        &mut Targets::new(args),
    )
    .c_return()
}

/// [`sscanf`] with destinations as trailing arguments.
///
/// ```
/// use xj_scanf::sscanf;
///
/// let mut x: i32 = 0;
/// let mut name = String::new();
/// assert_eq!(sscanf!("42 Alice", "%d %s", &mut x, &mut name), 2);
/// assert_eq!((x, name.as_str()), (42, "Alice"));
/// ```
#[macro_export]
macro_rules! sscanf {
    ($input:expr, $fmt:expr $(,)?) => {
        $crate::sscanf($input, $fmt, &mut [])
    };
    ($input:expr, $fmt:expr, $($arg:expr),+ $(,)?) => {
        $crate::sscanf($input, $fmt, &mut [$($arg as &mut dyn $crate::ScanTarget),+])
    };
}

/// [`bscanf`] with destinations as trailing arguments.
///
/// ```
/// use xj_scanf::bscanf;
///
/// let mut x: i32 = 0;
/// let mut y: f32 = 0.0;
/// assert_eq!(bscanf!(b"42 3.14", "%d %f", &mut x, &mut y), 2);
/// assert_eq!(x, 42);
/// ```
#[macro_export]
macro_rules! bscanf {
    ($input:expr, $fmt:expr $(,)?) => {
        $crate::bscanf($input, $fmt, &mut [])
    };
    ($input:expr, $fmt:expr, $($arg:expr),+ $(,)?) => {
        $crate::bscanf($input, $fmt, &mut [$($arg as &mut dyn $crate::ScanTarget),+])
    };
}

/// [`brscanf`] with destinations as trailing arguments.
///
/// ```
/// use xj_scanf::brscanf;
/// use std::io::Cursor;
///
/// let mut x: i32 = 0;
/// let mut y: f32 = 0.0;
/// assert_eq!(brscanf!(Cursor::new("42 3.14"), "%d %f", &mut x, &mut y), 2);
/// assert_eq!(x, 42);
/// ```
#[macro_export]
macro_rules! brscanf {
    ($reader:expr, $fmt:expr $(,)?) => {
        $crate::brscanf($reader, $fmt, &mut [])
    };
    ($reader:expr, $fmt:expr, $($arg:expr),+ $(,)?) => {
        $crate::brscanf($reader, $fmt, &mut [$($arg as &mut dyn $crate::ScanTarget),+])
    };
}
