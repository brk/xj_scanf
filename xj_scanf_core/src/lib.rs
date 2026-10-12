//! The C `scanf` format grammar and its destination requirements.
//!
//! This crate parses scanning formats into [`Directive`]s and maps each
//! directive to the C destination it requires ([`Requirement`]). It has no
//! input, numeric, or destination code, so a translator can analyze literal
//! formats with exactly the rules that the runtime engine (`xj_scanf`) and
//! its stream front ends apply.
//!
//! Formats are bytes and need not be UTF-8. [`Format`] stops at the first NUL
//! or the end of the given slice.
//!
//! ```
//! use xj_scanf_core::{Conv, DataModel, Format, IntKind, Item, Requirement, Slot};
//!
//! let items: Vec<_> = Format::new(b"%hhd %*s%[a-z]").map(|r| r.unwrap().1).collect();
//! let Item::Directive(d) = &items[0] else { panic!() };
//! assert_eq!(d.requirement(), Some(Requirement::Int { kind: IntKind::Char, signed: true }));
//! assert!(matches!(items[1], Item::Space));
//! let Item::Directive(s) = &items[2] else { panic!() };
//! assert!(s.suppress && s.requirement().is_none());
//! let Item::Directive(set) = &items[3] else { panic!() };
//! assert!(matches!(&set.conv, Conv::Set(bytes) if bytes.contains(b'q')));
//!
//! // `%ld` accepts a `long long` slot on LP64, but not on ILP32.
//! let ld = Requirement::Int { kind: IntKind::Long, signed: true };
//! assert!(ld.accepts(Slot::Int(IntKind::LongLong), &DataModel::LP64));
//! assert!(!ld.accepts(Slot::Int(IntKind::LongLong), &DataModel::ILP32));
//! ```
#![no_std]

use core::fmt;
use core::num::NonZeroUsize;

pub use xj_bytes::c_bytes;

/// A length modifier. `l` and `L` are kept apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LengthMod {
    None,
    /// `hh`
    Hh,
    /// `h`
    H,
    /// `l`
    L,
    /// `ll`
    Ll,
    /// `j`
    J,
    /// `z`
    Z,
    /// `t`
    T,
    /// `L` (long double). Rejected until long double is implemented.
    BigL,
}

/// A conversion specifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Conv {
    /// `%d` (base 10, signed), `%i` (base 0, signed), `%o` (8), `%u` (10),
    /// `%x`/`%X` (16).
    Int { base: u8, signed: bool },
    /// `%a %A %e %E %f %F %g %G`, which share one input grammar.
    Float,
    /// `%s`
    Str,
    /// `%c`
    Chars,
    /// `%[...]`, with any `^` inversion already applied.
    Set(ByteSet),
    /// `%n`
    Count,
    /// `%%`
    Percent,
}

/// A membership bitmap for `%[`, stored inline.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ByteSet([u64; 4]);

impl ByteSet {
    pub const EMPTY: ByteSet = ByteSet([0; 4]);

    pub fn contains(&self, byte: u8) -> bool {
        self.0[usize::from(byte >> 6)] & (1 << (byte & 63)) != 0
    }

    pub fn insert(&mut self, byte: u8) {
        self.0[usize::from(byte >> 6)] |= 1 << (byte & 63);
    }

    pub fn insert_range(&mut self, start: u8, end: u8) {
        for byte in start..=end {
            self.insert(byte);
        }
    }

    pub fn invert(&mut self) {
        for word in &mut self.0 {
            *word = !*word;
        }
    }
}

impl fmt::Debug for ByteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set()
            .entries((0..=255u8).filter(|&b| self.contains(b)))
            .finish()
    }
}

/// One conversion specification, from `%` through its conversion specifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Directive {
    /// `*`: the conversion reads input but claims no destination.
    pub suppress: bool,
    /// The maximum field width. Zero is not a valid width.
    pub width: Option<NonZeroUsize>,
    pub len: LengthMod,
    pub conv: Conv,
}

impl Directive {
    /// The destination this directive claims, or `None` for suppressed
    /// conversions and `%%`.
    pub fn requirement(&self) -> Option<Requirement> {
        if self.suppress {
            return None;
        }
        Some(match self.conv {
            Conv::Int { signed, .. } => Requirement::Int {
                kind: self.len.int_kind()?,
                signed,
            },
            Conv::Float => match self.len {
                LengthMod::None => Requirement::Float,
                LengthMod::L => Requirement::Double,
                _ => return None,
            },
            Conv::Str | Conv::Set(_) => Requirement::Str,
            Conv::Chars => Requirement::Chars(self.width.unwrap_or(NonZeroUsize::MIN)),
            Conv::Count => Requirement::Count(self.len.int_kind()?),
            Conv::Percent => return None,
        })
    }

    /// Whether leading input whitespace is skipped before the input item.
    pub fn skips_space(&self) -> bool {
        !matches!(self.conv, Conv::Chars | Conv::Set(_) | Conv::Count)
    }
}

impl LengthMod {
    /// The integer kind selected by this modifier for integer conversions
    /// and `%n`. `None` for `L`.
    pub fn int_kind(self) -> Option<IntKind> {
        Some(match self {
            LengthMod::None => IntKind::Int,
            LengthMod::Hh => IntKind::Char,
            LengthMod::H => IntKind::Short,
            LengthMod::L => IntKind::Long,
            LengthMod::Ll => IntKind::LongLong,
            LengthMod::J => IntKind::IntMax,
            LengthMod::Z => IntKind::Size,
            LengthMod::T => IntKind::PtrDiff,
            LengthMod::BigL => return None,
        })
    }
}

/// The C destination a non-suppressed directive stores into.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Requirement {
    /// `%d %i %u %o %x` with their length.
    Int { kind: IntKind, signed: bool },
    /// Floating conversions with no length modifier.
    Float,
    /// Floating conversions with `l`.
    Double,
    /// `%s` and `%[`: terminated bytes.
    Str,
    /// `%Nc`: N bytes, no terminator (default 1).
    Chars(NonZeroUsize),
    /// `%n`: any integer slot of this width.
    Count(IntKind),
}

/// The C integer types named by length modifiers and destination types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntKind {
    Char,
    Short,
    Int,
    Long,
    LongLong,
    IntMax,
    Size,
    PtrDiff,
}

/// Integer widths in bytes for a C data model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DataModel {
    pub short: u8,
    pub int: u8,
    pub long: u8,
    pub long_long: u8,
    pub intmax: u8,
    pub size: u8,
    pub ptrdiff: u8,
}

impl DataModel {
    /// 64-bit Unix.
    pub const LP64: DataModel = DataModel {
        short: 2,
        int: 4,
        long: 8,
        long_long: 8,
        intmax: 8,
        size: 8,
        ptrdiff: 8,
    };
    /// 32-bit targets, including x32.
    pub const ILP32: DataModel = DataModel {
        short: 2,
        int: 4,
        long: 4,
        long_long: 8,
        intmax: 8,
        size: 4,
        ptrdiff: 4,
    };
    /// 64-bit Windows.
    pub const LLP64: DataModel = DataModel {
        short: 2,
        int: 4,
        long: 4,
        long_long: 8,
        intmax: 8,
        size: 8,
        ptrdiff: 8,
    };
    /// The host's model, from `core::ffi`. `intmax_t` is 64 bits on every
    /// supported target.
    pub const HOST: DataModel = DataModel {
        short: size_of::<core::ffi::c_short>() as u8,
        int: size_of::<core::ffi::c_int>() as u8,
        long: size_of::<core::ffi::c_long>() as u8,
        long_long: size_of::<core::ffi::c_longlong>() as u8,
        intmax: 8,
        size: size_of::<usize>() as u8,
        ptrdiff: size_of::<isize>() as u8,
    };

    /// The model for an LLVM target triple, such as a translator's target.
    pub fn for_target(triple: &str) -> DataModel {
        let arch = triple.split('-').next().unwrap_or("");
        let wide = arch.contains("64") || arch == "s390x";
        if !wide || triple.ends_with("x32") || triple.contains("gnux32") {
            DataModel::ILP32
        } else if triple.contains("windows") {
            DataModel::LLP64
        } else {
            DataModel::LP64
        }
    }

    pub fn width(&self, kind: IntKind) -> u8 {
        match kind {
            IntKind::Char => 1,
            IntKind::Short => self.short,
            IntKind::Int => self.int,
            IntKind::Long => self.long,
            IntKind::LongLong => self.long_long,
            IntKind::IntMax => self.intmax,
            IntKind::Size => self.size,
            IntKind::PtrDiff => self.ptrdiff,
        }
    }
}

/// The class and width of a destination, for the compatibility rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Slot {
    /// An integer object of this C type, of either signedness.
    Int(IntKind),
    Float,
    Double,
    /// A byte region (a `char` array or bounded string destination).
    Bytes,
}

impl Requirement {
    /// The compatibility rule. A destination is accepted when its class
    /// matches and its width equals the requirement's width under `model`.
    ///
    /// - Signedness differences and equal-width rank differences are
    ///   accepted.
    /// - `%n` accepts any integer slot of its width.
    /// - `%c` with width 1 also accepts a 1-byte integer slot: C's `char`
    ///   object is the conventional `%c` destination.
    /// - Width and class differences are rejected.
    pub fn accepts(self, slot: Slot, model: &DataModel) -> bool {
        match (self, slot) {
            (Requirement::Int { kind, .. } | Requirement::Count(kind), Slot::Int(dest)) => {
                model.width(kind) == model.width(dest)
            }
            (Requirement::Float, Slot::Float) | (Requirement::Double, Slot::Double) => true,
            (Requirement::Str | Requirement::Chars(_), Slot::Bytes) => true,
            (Requirement::Chars(n), Slot::Int(dest)) => n.get() == 1 && model.width(dest) == 1,
            _ => false,
        }
    }
}

/// One format item.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Item {
    /// A run of format whitespace, which matches any amount of input
    /// whitespace, including none.
    Space,
    /// An ordinary byte, which must match the next input byte.
    Byte(u8),
    Directive(Directive),
}

/// Why a directive is invalid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormatErrorKind {
    /// The format ends inside a directive.
    Incomplete,
    /// An unknown conversion specifier.
    UnknownConversion(u8),
    /// A length modifier that does not fit its conversion.
    BadLength,
    /// A zero or overflowing field width.
    BadWidth,
    /// `%[` without a closing `]`.
    UnterminatedSet,
    /// `%%` with a flag, width or length, or `%n` with `*` or a width.
    BadSpecification,
    /// A valid C directive that this implementation does not support yet:
    /// `%p`, long double (`L`) and wide conversions (`%lc`, `%ls`, `%l[`).
    Unsupported,
}

/// An invalid directive, at the byte offset of its `%`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FormatError {
    pub offset: usize,
    pub kind: FormatErrorKind,
}

impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match self.kind {
            FormatErrorKind::Incomplete => "incomplete directive",
            FormatErrorKind::UnknownConversion(_) => "unknown conversion",
            FormatErrorKind::BadLength => "length modifier does not fit the conversion",
            FormatErrorKind::BadWidth => "invalid field width",
            FormatErrorKind::UnterminatedSet => "unterminated scanset",
            FormatErrorKind::BadSpecification => "invalid conversion specification",
            FormatErrorKind::Unsupported => "unsupported directive",
        };
        write!(f, "{what} at format offset {}", self.offset)?;
        if let FormatErrorKind::UnknownConversion(byte) = self.kind {
            write!(f, " ({:?})", byte as char)?;
        }
        Ok(())
    }
}

impl core::error::Error for FormatError {}

/// C's whitespace in the C locale.
pub fn is_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

/// A lazy iterator over the items of a format, yielding each item with the
/// byte offset at which it starts. It stops after the first error.
#[derive(Clone, Debug)]
pub struct Format<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Format<'a> {
    /// Iterates over `format` through its first NUL or end.
    pub fn new(format: &'a [u8]) -> Self {
        Format {
            bytes: c_bytes(format),
            pos: 0,
        }
    }

    /// Checks a whole format, returning its first error.
    pub fn validate(format: &[u8]) -> Result<(), FormatError> {
        Format::new(format).try_for_each(|item| item.map(drop))
    }

    /// The non-suppressed destinations claimed by `format`, in order.
    pub fn requirements(
        format: &'a [u8],
    ) -> impl Iterator<Item = Result<Requirement, FormatError>> + 'a {
        Format::new(format).filter_map(|item| match item {
            Ok((_, Item::Directive(d))) => d.requirement().map(Ok),
            Ok(_) => None,
            Err(e) => Some(Err(e)),
        })
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn directive(&mut self, start: usize) -> Result<Directive, FormatError> {
        let err = |kind| FormatError {
            offset: start,
            kind,
        };
        let suppress = self.peek() == Some(b'*');
        self.pos += usize::from(suppress);
        let mut width: Option<usize> = None;
        while let Some(digit @ b'0'..=b'9') = self.peek() {
            self.pos += 1;
            width = Some(
                width
                    .unwrap_or(0)
                    .checked_mul(10)
                    .and_then(|w| w.checked_add(usize::from(digit - b'0')))
                    .ok_or(err(FormatErrorKind::BadWidth))?,
            );
        }
        let width = match width {
            Some(w) => Some(NonZeroUsize::new(w).ok_or(err(FormatErrorKind::BadWidth))?),
            None => None,
        };
        let mut take = |b: u8| {
            let hit = self.bytes.get(self.pos) == Some(&b);
            self.pos += usize::from(hit);
            hit
        };
        let len = if take(b'h') {
            if take(b'h') {
                LengthMod::Hh
            } else {
                LengthMod::H
            }
        } else if take(b'l') {
            if take(b'l') {
                LengthMod::Ll
            } else {
                LengthMod::L
            }
        } else if take(b'j') {
            LengthMod::J
        } else if take(b'z') {
            LengthMod::Z
        } else if take(b't') {
            LengthMod::T
        } else if take(b'L') {
            LengthMod::BigL
        } else {
            LengthMod::None
        };
        let spec = self.peek().ok_or(err(FormatErrorKind::Incomplete))?;
        self.pos += 1;
        let conv = match spec {
            b'd' => Conv::Int {
                base: 10,
                signed: true,
            },
            b'i' => Conv::Int {
                base: 0,
                signed: true,
            },
            b'o' => Conv::Int {
                base: 8,
                signed: false,
            },
            b'u' => Conv::Int {
                base: 10,
                signed: false,
            },
            b'x' | b'X' => Conv::Int {
                base: 16,
                signed: false,
            },
            b'a' | b'A' | b'e' | b'E' | b'f' | b'F' | b'g' | b'G' => Conv::Float,
            b's' => Conv::Str,
            b'c' => Conv::Chars,
            b'n' => Conv::Count,
            b'%' => Conv::Percent,
            b'[' => Conv::Set(
                self.scanset()
                    .ok_or(err(FormatErrorKind::UnterminatedSet))?,
            ),
            b'p' => return Err(err(FormatErrorKind::Unsupported)),
            other => return Err(err(FormatErrorKind::UnknownConversion(other))),
        };
        match (conv, len) {
            (Conv::Int { .. } | Conv::Count, LengthMod::BigL) => {
                return Err(err(FormatErrorKind::BadLength));
            }
            (Conv::Int { .. } | Conv::Count, _) => {}
            (Conv::Float, LengthMod::None | LengthMod::L) => {}
            (Conv::Float, LengthMod::BigL) => return Err(err(FormatErrorKind::Unsupported)),
            (Conv::Str | Conv::Chars | Conv::Set(_), LengthMod::None) => {}
            (Conv::Str | Conv::Chars | Conv::Set(_), LengthMod::L) => {
                return Err(err(FormatErrorKind::Unsupported));
            }
            (Conv::Percent, LengthMod::None) => {}
            _ => return Err(err(FormatErrorKind::BadLength)),
        }
        // The standard leaves `%*n`, `%5n` and anything but a bare `%%`
        // undefined; reject them rather than choosing a meaning.
        if matches!(conv, Conv::Percent | Conv::Count) && (suppress || width.is_some()) {
            return Err(err(FormatErrorKind::BadSpecification));
        }
        Ok(Directive {
            suppress,
            width,
            len,
            conv,
        })
    }

    /// Parses a scanset after its `[`. `]` is literal when it comes first,
    /// `-` is literal when it comes first or last, and a reversed range is
    /// taken literally. After a range, a following `-` may extend from its
    /// end, as in libc.
    fn scanset(&mut self) -> Option<ByteSet> {
        let invert = self.peek() == Some(b'^');
        self.pos += usize::from(invert);
        let mut set = ByteSet::EMPTY;
        let mut previous: Option<u8> = None;
        let mut first = true;
        loop {
            let byte = self.peek()?;
            self.pos += 1;
            if byte == b']' && !first {
                break;
            }
            if let (b'-', false, Some(start)) = (byte, first, previous) {
                if let Some(end) = self.peek().filter(|&end| end != b']' && start <= end) {
                    self.pos += 1;
                    set.insert_range(start, end);
                    previous = Some(end);
                    continue;
                }
            }
            set.insert(byte);
            previous = Some(byte);
            first = false;
        }
        if invert {
            set.invert();
        }
        Some(set)
    }
}

impl Iterator for Format<'_> {
    type Item = Result<(usize, Item), FormatError>;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.pos;
        let byte = self.peek()?;
        self.pos += 1;
        if is_space(byte) {
            while self.peek().is_some_and(is_space) {
                self.pos += 1;
            }
            return Some(Ok((start, Item::Space)));
        }
        if byte != b'%' {
            return Some(Ok((start, Item::Byte(byte))));
        }
        match self.directive(start) {
            Ok(d) => Some(Ok((start, Item::Directive(d)))),
            Err(e) => {
                self.pos = self.bytes.len();
                Some(Err(e))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate std;
    use std::vec::Vec;

    fn one(format: &[u8]) -> Result<Directive, FormatError> {
        let mut items = Format::new(format);
        match items.next().unwrap()? {
            (_, Item::Directive(d)) => Ok(d),
            other => panic!("{other:?}"),
        }
    }

    fn kind(format: &[u8]) -> FormatErrorKind {
        one(format).unwrap_err().kind
    }

    #[test]
    fn length_modifiers_select_int_kinds() {
        for (format, kind) in [
            (&b"%hhd"[..], IntKind::Char),
            (b"%hd", IntKind::Short),
            (b"%d", IntKind::Int),
            (b"%ld", IntKind::Long),
            (b"%lld", IntKind::LongLong),
            (b"%jd", IntKind::IntMax),
            (b"%zd", IntKind::Size),
            (b"%td", IntKind::PtrDiff),
        ] {
            assert_eq!(
                one(format).unwrap().requirement(),
                Some(Requirement::Int { kind, signed: true }),
                "{format:?}"
            );
        }
        assert_eq!(
            one(b"%hhn").unwrap().requirement(),
            Some(Requirement::Count(IntKind::Char))
        );
        assert_eq!(
            one(b"%hu").unwrap().requirement(),
            Some(Requirement::Int {
                kind: IntKind::Short,
                signed: false
            })
        );
    }

    #[test]
    fn float_and_byte_requirements() {
        assert_eq!(one(b"%f").unwrap().requirement(), Some(Requirement::Float));
        assert_eq!(
            one(b"%lg").unwrap().requirement(),
            Some(Requirement::Double)
        );
        assert_eq!(one(b"%s").unwrap().requirement(), Some(Requirement::Str));
        assert_eq!(one(b"%[a]").unwrap().requirement(), Some(Requirement::Str));
        assert_eq!(
            one(b"%c").unwrap().requirement(),
            Some(Requirement::Chars(NonZeroUsize::new(1).unwrap()))
        );
        assert_eq!(
            one(b"%7c").unwrap().requirement(),
            Some(Requirement::Chars(NonZeroUsize::new(7).unwrap()))
        );
        assert_eq!(one(b"%*d").unwrap().requirement(), None);
        assert_eq!(one(b"%%").unwrap().requirement(), None);
    }

    #[test]
    fn invalid_and_unsupported_directives() {
        assert_eq!(kind(b"%p"), FormatErrorKind::Unsupported);
        assert_eq!(kind(b"%Lf"), FormatErrorKind::Unsupported);
        assert_eq!(kind(b"%lc"), FormatErrorKind::Unsupported);
        assert_eq!(kind(b"%ls"), FormatErrorKind::Unsupported);
        assert_eq!(kind(b"%l[a]"), FormatErrorKind::Unsupported);
        assert_eq!(kind(b"%Ld"), FormatErrorKind::BadLength);
        assert_eq!(kind(b"%hf"), FormatErrorKind::BadLength);
        assert_eq!(kind(b"%hs"), FormatErrorKind::BadLength);
        assert_eq!(kind(b"%h%"), FormatErrorKind::BadLength);
        assert_eq!(kind(b"%y"), FormatErrorKind::UnknownConversion(b'y'));
        assert_eq!(kind(b"%ms"), FormatErrorKind::UnknownConversion(b'm'));
        assert_eq!(kind(b"%1$d"), FormatErrorKind::UnknownConversion(b'$'));
        assert_eq!(kind(b"%"), FormatErrorKind::Incomplete);
        assert_eq!(kind(b"%ll"), FormatErrorKind::Incomplete);
        assert_eq!(kind(b"%0d"), FormatErrorKind::BadWidth);
        assert_eq!(
            kind(b"%99999999999999999999999d"),
            FormatErrorKind::BadWidth
        );
        assert_eq!(kind(b"%[abc"), FormatErrorKind::UnterminatedSet);
        assert_eq!(kind(b"%[]"), FormatErrorKind::UnterminatedSet);
        assert_eq!(kind(b"%*n"), FormatErrorKind::BadSpecification);
        assert_eq!(kind(b"%3n"), FormatErrorKind::BadSpecification);
        assert_eq!(kind(b"%*%"), FormatErrorKind::BadSpecification);
        assert_eq!(kind(b"%2%"), FormatErrorKind::BadSpecification);
    }

    #[test]
    fn errors_report_the_directive_offset_and_stop() {
        let mut items = Format::new(b"ab %d %q %d");
        let errors: Vec<_> = items.by_ref().filter_map(Result::err).collect();
        assert_eq!(
            errors,
            [FormatError {
                offset: 6,
                kind: FormatErrorKind::UnknownConversion(b'q')
            }]
        );
        assert!(items.next().is_none());
        assert_eq!(Format::validate(b"%d %s").map_err(|e| e.offset), Ok(()));
    }

    #[test]
    fn items_split_space_bytes_and_directives() {
        let items: Vec<_> = Format::new(b" \t\nx%5s\0%d").map(Result::unwrap).collect();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], (0, Item::Space));
        assert_eq!(items[1], (3, Item::Byte(b'x')));
        let (offset, Item::Directive(d)) = items[2] else {
            panic!()
        };
        assert_eq!(offset, 4);
        assert_eq!(d.width, NonZeroUsize::new(5));
        assert_eq!(d.conv, Conv::Str);
    }

    fn set(format: &[u8]) -> ByteSet {
        match one(format).unwrap().conv {
            Conv::Set(set) => set,
            other => panic!("{other:?}"),
        }
    }

    fn members(set: ByteSet) -> Vec<u8> {
        (0..=255u8).filter(|&b| set.contains(b)).collect()
    }

    #[test]
    fn scanset_ranges_and_literals() {
        assert_eq!(members(set(b"%[a-e]")), b"abcde");
        assert_eq!(members(set(b"%[]a]")), b"]a");
        assert_eq!(members(set(b"%[^]a]")).len(), 254);
        assert_eq!(members(set(b"%[-a]")), b"-a");
        assert_eq!(members(set(b"%[a-]")), b"-a");
        assert_eq!(members(set(b"%[z-a]")), b"-az");
        assert_eq!(members(set(b"%[a-c-e]")), b"abcde");
        assert_eq!(members(set(b"%[zx-]")), b"-xz");
        assert!(!set(b"%[^\n]").contains(b'\n'));
        assert!(set(b"%[^\n]").contains(0xff));
    }

    #[test]
    fn compatibility_rule() {
        let lp64 = DataModel::LP64;
        let ilp32 = DataModel::ILP32;
        let int = Requirement::Int {
            kind: IntKind::Int,
            signed: true,
        };
        let size = Requirement::Int {
            kind: IntKind::Size,
            signed: false,
        };
        assert!(int.accepts(Slot::Int(IntKind::Int), &lp64));
        assert!(!int.accepts(Slot::Int(IntKind::Short), &lp64));
        assert!(!int.accepts(Slot::Int(IntKind::Long), &lp64));
        assert!(int.accepts(Slot::Int(IntKind::Long), &ilp32));
        assert!(size.accepts(Slot::Int(IntKind::Long), &lp64));
        assert!(!size.accepts(Slot::Int(IntKind::LongLong), &ilp32));
        assert!(!int.accepts(Slot::Bytes, &lp64));
        assert!(!int.accepts(Slot::Float, &lp64));
        assert!(Requirement::Float.accepts(Slot::Float, &lp64));
        assert!(!Requirement::Float.accepts(Slot::Double, &lp64));
        assert!(!Requirement::Double.accepts(Slot::Float, &lp64));
        assert!(Requirement::Str.accepts(Slot::Bytes, &lp64));
        assert!(!Requirement::Str.accepts(Slot::Int(IntKind::Char), &lp64));
        let one = Requirement::Chars(NonZeroUsize::MIN);
        let two = Requirement::Chars(NonZeroUsize::new(2).unwrap());
        assert!(one.accepts(Slot::Int(IntKind::Char), &lp64));
        assert!(!two.accepts(Slot::Int(IntKind::Char), &lp64));
        assert!(!one.accepts(Slot::Int(IntKind::Int), &lp64));
        assert!(Requirement::Count(IntKind::Long).accepts(Slot::Int(IntKind::Size), &lp64));
        assert!(!Requirement::Count(IntKind::Char).accepts(Slot::Int(IntKind::Int), &lp64));
    }

    #[test]
    fn target_data_models() {
        assert_eq!(
            DataModel::for_target("x86_64-unknown-linux-gnu"),
            DataModel::LP64
        );
        assert_eq!(
            DataModel::for_target("aarch64-apple-darwin"),
            DataModel::LP64
        );
        assert_eq!(
            DataModel::for_target("x86_64-pc-windows-msvc"),
            DataModel::LLP64
        );
        assert_eq!(
            DataModel::for_target("i686-unknown-linux-gnu"),
            DataModel::ILP32
        );
        assert_eq!(
            DataModel::for_target("x86_64-unknown-linux-gnux32"),
            DataModel::ILP32
        );
        assert_eq!(
            DataModel::for_target("armv7-unknown-linux-gnueabihf"),
            DataModel::ILP32
        );
        assert_eq!(
            DataModel::for_target("s390x-unknown-linux-gnu"),
            DataModel::LP64
        );
    }
}
