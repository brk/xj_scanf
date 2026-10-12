//! Safe destinations: [`ScanTarget`] and its implementations.

use xj_bytes::CStrDest;
use xj_scanf_core::{Conv, DataModel, Directive, IntKind, Requirement, Slot};

use crate::{ScanArgs, StoreError, Value};

/// A safe destination for one conversion.
///
/// The reference's type is the destination type, so the compatibility rule
/// needs no extra tags: `%d` accepts any 32-bit integer, `%lf` only `f64`,
/// `%s` only byte destinations, and so on (see
/// [`Requirement::accepts`]).
pub trait ScanTarget {
    /// Validates this destination for `d` before the directive reads any
    /// input. Returns the byte limit for `%s`/`%[` (room is kept for the
    /// terminator) and `%c` (no terminator), or `None` for unbounded
    /// storage or a non-byte destination.
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError>;

    /// Stores a completed conversion. A failed store stops the scan and
    /// does not count as an assignment.
    fn store(&mut self, d: &Directive, value: Value<'_>) -> Result<(), StoreError>;
}

fn requirement(d: &Directive) -> Result<Requirement, StoreError> {
    d.requirement().ok_or(StoreError::TypeMismatch)
}

/// Converts a scanned integer to a signed destination of `bits` bits.
///
/// Representable values are stored exactly, including the minimum.
/// Anything else saturates to the minimum or maximum by its sign.
pub fn signed_value(neg: bool, mag: u64, overflow: bool, bits: u32) -> i64 {
    let max = (1u64 << (bits - 1)) - 1;
    let min = -(max as i64) - 1;
    match (neg, overflow) {
        (false, true) => max as i64,
        (true, true) => min,
        (false, false) => mag.min(max) as i64,
        (true, false) if mag <= max + 1 => (mag as i64).wrapping_neg(),
        (true, false) => min,
    }
}

/// Converts a scanned integer to an unsigned destination of `bits` bits.
///
/// A representable magnitude is converted with its sign modulo the
/// destination's range (`-1` stores the maximum). A magnitude beyond the
/// maximum, or an overflowed accumulator, stores the maximum for either
/// sign.
pub fn unsigned_value(neg: bool, mag: u64, overflow: bool, bits: u32) -> u64 {
    let max = u64::MAX >> (64 - bits);
    if overflow || mag > max {
        max
    } else if neg {
        mag.wrapping_neg() & max
    } else {
        mag
    }
}

/// The bits stored for an integer conversion into a `bits`-bit destination
/// of the given signedness.
///
/// A value representable in the destination's type is stored exactly. An
/// unsigned directive whose value is representable in its own type (`%hhu`
/// with 255 into `signed char`, `%u` with 4294967295 into `int`) stores that
/// bit pattern, as when C accesses the object through the other signedness.
/// Anything else follows [`signed_value`] or [`unsigned_value`].
pub fn int_bits(d: &Directive, value: Value<'_>, signed: bool, bits: u32) -> Option<u64> {
    let (neg, mag, overflow) = match value {
        Value::Int { neg, mag, overflow } => (neg, mag, overflow),
        Value::Count(n) => (false, n as u64, false),
        Value::Bytes(&[byte]) => (false, u64::from(byte), false),
        _ => return None,
    };
    let mask = u64::MAX >> (64 - bits);
    if !signed {
        return Some(unsigned_value(neg, mag, overflow, bits));
    }
    let limit = 1u64 << (bits - 1);
    let fits = !overflow && if neg { mag <= limit } else { mag < limit };
    let unsigned_fits =
        matches!(d.conv, Conv::Int { signed: false, .. }) && !overflow && mag <= mask;
    Some(if fits || !unsigned_fits {
        signed_value(neg, mag, overflow, bits) as u64 & mask
    } else {
        unsigned_value(neg, mag, overflow, bits)
    })
}

macro_rules! int_target {
    ($signed:literal: $($ty:ty => $kind:expr),*) => {$(
        impl ScanTarget for $ty {
            fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
                let req = requirement(d)?;
                if !req.accepts(Slot::Int($kind), &DataModel::HOST) {
                    return Err(StoreError::TypeMismatch);
                }
                // A 1-byte integer is C's `char` object for `%c`.
                Ok(matches!(req, Requirement::Chars(_)).then_some(1))
            }

            fn store(&mut self, d: &Directive, value: Value<'_>) -> Result<(), StoreError> {
                let bits = int_bits(d, value, $signed, <$ty>::BITS)
                    .ok_or(StoreError::TypeMismatch)?;
                *self = bits as $ty;
                Ok(())
            }
        }
    )*};
}

int_target!(true: i8 => IntKind::Char, i16 => IntKind::Short, i32 => IntKind::Int,
    i64 => IntKind::LongLong, isize => IntKind::PtrDiff);
int_target!(false: u8 => IntKind::Char, u16 => IntKind::Short, u32 => IntKind::Int,
    u64 => IntKind::LongLong, usize => IntKind::Size);

macro_rules! float_target {
    ($ty:ty, $req:ident, $value:ident) => {
        impl ScanTarget for $ty {
            fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
                match requirement(d)? {
                    Requirement::$req => Ok(None),
                    _ => Err(StoreError::TypeMismatch),
                }
            }

            fn store(&mut self, _: &Directive, value: Value<'_>) -> Result<(), StoreError> {
                match value {
                    Value::$value(v) => *self = v,
                    _ => return Err(StoreError::TypeMismatch),
                }
                Ok(())
            }
        }
    };
}

float_target!(f32, Float, Float32);
float_target!(f64, Double, Float64);

/// Bounded byte storage. `%s` and `%[` store at most `max_len()` bytes and
/// a terminator; `%Nc` needs `region_len() >= N` and stores no terminator.
impl ScanTarget for CStrDest<'_> {
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
        match requirement(d)? {
            Requirement::Str => Ok(Some(self.max_len())),
            Requirement::Chars(_) => Ok(Some(self.region_len())),
            _ => Err(StoreError::TypeMismatch),
        }
    }

    fn store(&mut self, d: &Directive, value: Value<'_>) -> Result<(), StoreError> {
        let Value::Bytes(bytes) = value else {
            return Err(StoreError::TypeMismatch);
        };
        if d.conv == Conv::Chars {
            let region = self.region_mut();
            region
                .get_mut(..bytes.len())
                .ok_or(StoreError::Capacity)?
                .copy_from_slice(bytes);
        } else {
            if bytes.len() > self.max_len() {
                return Err(StoreError::Capacity);
            }
            self.write_truncated(bytes);
        }
        Ok(())
    }
}

/// A byte array is `char buf[N]`: a bounded destination of C size N.
impl<const N: usize> ScanTarget for [u8; N] {
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
        CStrDest::from(self).prepare(d)
    }

    fn store(&mut self, d: &Directive, value: Value<'_>) -> Result<(), StoreError> {
        CStrDest::from(self).store(d, value)
    }
}

/// A mutable byte slice of length N is a bounded destination of C size N.
impl ScanTarget for &mut [u8] {
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
        CStrDest::from(&mut **self).prepare(d)
    }

    fn store(&mut self, d: &Directive, value: Value<'_>) -> Result<(), StoreError> {
        CStrDest::from(&mut **self).store(d, value)
    }
}

/// An owned, growable byte payload. The field replaces its contents, with no
/// terminator. Borrow its slice to select bounded storage instead.
impl ScanTarget for Vec<u8> {
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
        match requirement(d)? {
            Requirement::Str | Requirement::Chars(_) => Ok(None),
            _ => Err(StoreError::TypeMismatch),
        }
    }

    fn store(&mut self, _: &Directive, value: Value<'_>) -> Result<(), StoreError> {
        let Value::Bytes(bytes) = value else {
            return Err(StoreError::TypeMismatch);
        };
        self.clear();
        self.extend_from_slice(bytes);
        Ok(())
    }
}

/// An owned string. A field that is not valid UTF-8 fails with
/// [`StoreError::TypeMismatch`] and leaves the string unchanged.
impl ScanTarget for String {
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
        match requirement(d)? {
            Requirement::Str | Requirement::Chars(_) => Ok(None),
            _ => Err(StoreError::TypeMismatch),
        }
    }

    fn store(&mut self, _: &Directive, value: Value<'_>) -> Result<(), StoreError> {
        let Value::Bytes(bytes) = value else {
            return Err(StoreError::TypeMismatch);
        };
        let text = std::str::from_utf8(bytes).map_err(|_| StoreError::TypeMismatch)?;
        self.clear();
        self.push_str(text);
        Ok(())
    }
}

/// The [`ScanArgs`] adapter over safe destinations, claimed in order.
pub struct Targets<'a, 'b> {
    targets: &'a mut [&'b mut dyn ScanTarget],
    next: usize,
}

impl<'a, 'b> Targets<'a, 'b> {
    pub fn new(targets: &'a mut [&'b mut dyn ScanTarget]) -> Self {
        Targets { targets, next: 0 }
    }
}

impl ScanArgs for Targets<'_, '_> {
    fn prepare(&mut self, d: &Directive) -> Result<Option<usize>, StoreError> {
        let target = self.targets.get_mut(self.next).ok_or(StoreError::Missing)?;
        let limit = target.prepare(d)?;
        self.next += 1;
        Ok(limit)
    }

    fn store(&mut self, d: &Directive, value: Value<'_>) -> Result<(), StoreError> {
        let index = self.next.checked_sub(1).ok_or(StoreError::Missing)?;
        self.targets[index].store(d, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signed_policy() {
        assert_eq!(signed_value(true, 128, false, 8), -128);
        assert_eq!(signed_value(true, 129, false, 8), -128);
        assert_eq!(signed_value(false, 128, false, 8), 127);
        assert_eq!(signed_value(false, 5, true, 32), i32::MAX as i64);
        assert_eq!(signed_value(true, 5, true, 32), i32::MIN as i64);
        assert_eq!(signed_value(true, 1 << 63, false, 64), i64::MIN);
        assert_eq!(signed_value(true, (1 << 63) + 1, false, 64), i64::MIN);
        assert_eq!(signed_value(false, u64::MAX, false, 64), i64::MAX);
        assert_eq!(signed_value(true, 0, false, 32), 0);
    }

    #[test]
    fn unsigned_policy() {
        assert_eq!(unsigned_value(true, 1, false, 32), u32::MAX as u64);
        assert_eq!(unsigned_value(true, 128, false, 8), 128);
        assert_eq!(unsigned_value(true, 256, false, 8), 255);
        assert_eq!(unsigned_value(false, 256, false, 8), 255);
        assert_eq!(unsigned_value(false, 7, true, 16), 65535);
        assert_eq!(unsigned_value(true, 7, true, 16), 65535);
        assert_eq!(unsigned_value(true, 1, false, 64), u64::MAX);
        assert_eq!(unsigned_value(false, u64::MAX, false, 64), u64::MAX);
    }
}
