//! Conversion of validated floating tokens directly to the destination
//! precision.
//!
//! Decimal tokens use Rust's correctly rounded parsers for `f32` and `f64`,
//! so `%f` never rounds through `f64` first. Hexadecimal tokens are rounded
//! here, to nearest with ties to even, including subnormal results.

/// A token accepted by the scanner: an optional sign, then decimal digits
/// with an optional `.` and `e` exponent, or `0x` and hexadecimal digits
/// with an optional `.` and `p` exponent.
pub(crate) fn parse_f32(token: &[u8], hex: bool) -> f32 {
    if hex {
        let (neg, bits) = hex_bits(token, 24, -126, 127);
        f32::from_bits(bits as u32 | (u32::from(neg) << 31))
    } else {
        decimal(token).parse().expect("validated decimal token")
    }
}

pub(crate) fn parse_f64(token: &[u8], hex: bool) -> f64 {
    if hex {
        let (neg, bits) = hex_bits(token, 53, -1022, 1023);
        f64::from_bits(bits | (u64::from(neg) << 63))
    } else {
        decimal(token).parse().expect("validated decimal token")
    }
}

fn decimal(token: &[u8]) -> &str {
    std::str::from_utf8(token).expect("decimal tokens are ASCII")
}

/// The unsigned IEEE bits of a hexadecimal token, for a format with
/// `precision` significand bits (including the implicit bit) and the given
/// normal exponent range.
fn hex_bits(token: &[u8], precision: u32, emin: i64, emax: i64) -> (bool, u64) {
    let (neg, rest) = match token.first() {
        Some(b'-') => (true, &token[1..]),
        Some(b'+') => (false, &token[1..]),
        _ => (false, token),
    };
    let rest = &rest[2..]; // `0x`
    let mut mantissa = 0u64;
    let mut sticky = false;
    // The value is mantissa * 2^exp2, plus a nonzero tail if `sticky`.
    let mut exp2: i64 = 0;
    let mut fraction = false;
    let mut i = 0;
    while let Some(&byte) = rest.get(i) {
        i += 1;
        if byte == b'.' {
            fraction = true;
            continue;
        }
        let Some(digit) = (byte as char).to_digit(16) else {
            break;
        };
        if mantissa >> 60 == 0 {
            mantissa = mantissa << 4 | u64::from(digit);
            if fraction {
                exp2 -= 4;
            }
        } else {
            sticky |= digit != 0;
            if !fraction {
                exp2 += 4;
            }
        }
    }
    if let Some(exponent) = rest.get(i..).filter(|e| !e.is_empty()) {
        let (sign, digits) = match exponent.first() {
            Some(b'-') => (-1, &exponent[1..]),
            Some(b'+') => (1, &exponent[1..]),
            _ => (1, exponent),
        };
        // Saturate far beyond any finite or subnormal result.
        let value = digits
            .iter()
            .fold(0i64, |v, d| (v * 10 + i64::from(d - b'0')).min(1 << 20));
        exp2 += sign * value;
    }
    (neg, round(mantissa, sticky, exp2, precision, emin, emax))
}

fn round(mantissa: u64, sticky: bool, exp2: i64, precision: u32, emin: i64, emax: i64) -> u64 {
    let infinity = ((2 * emax + 1) as u64) << (precision - 1);
    if mantissa == 0 {
        return 0;
    }
    let zeros = mantissa.leading_zeros();
    let m = mantissa << zeros;
    // The value is in [2^e, 2^(e+1)).
    let mut e = exp2 - i64::from(zeros) + 63;
    if e > emax {
        return infinity;
    }
    let shift = 64 - i64::from(precision) + (emin - e).max(0);
    let (q, up) = match shift {
        65.. => (0, false),
        64 => (0, m > 1 << 63 || (m == 1 << 63 && sticky)),
        _ => {
            let q = m >> shift;
            let rem = m & ((1 << shift) - 1);
            let half = 1 << (shift - 1);
            (q, rem > half || (rem == half && (sticky || q & 1 == 1)))
        }
    };
    let mut q = q + u64::from(up);
    if e < emin {
        // Subnormal. Rounding up to 2^(precision - 1) encodes the smallest
        // normal number.
        return q;
    }
    if q >> precision != 0 {
        q >>= 1;
        e += 1;
        if e > emax {
            return infinity;
        }
    }
    ((e + emax) as u64) << (precision - 1) | (q & ((1 << (precision - 1)) - 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn h64(token: &str) -> f64 {
        parse_f64(token.as_bytes(), true)
    }

    fn h32(token: &str) -> f32 {
        parse_f32(token.as_bytes(), true)
    }

    #[test]
    fn hexadecimal_values() {
        assert_eq!(h64("0x1"), 1.0);
        assert_eq!(h64("0x1p4"), 16.0);
        assert_eq!(h64("-0x1.8p1"), -3.0);
        assert_eq!(h64("0x.8"), 0.5);
        assert_eq!(h64("0xA."), 10.0);
        assert_eq!(h64("0x0"), 0.0);
        assert!(h64("-0x0").is_sign_negative());
        assert_eq!(h64("0x1.fffffffffffffp1023"), f64::MAX);
        assert_eq!(h64("0x1p1024"), f64::INFINITY);
        assert_eq!(h64("0x1p-1074"), f64::from_bits(1));
        assert_eq!(h64("0x1p-1075"), 0.0);
        assert_eq!(h64("0x1.8p-1075"), f64::from_bits(1));
        assert_eq!(h64("0x1p-1022"), f64::MIN_POSITIVE);
        assert_eq!(h64("0x1.ffffffffffffffp-1023"), f64::MIN_POSITIVE);
        assert_eq!(
            h64("0x123456789abcdef0123p0"),
            0x123456789abcdef0123u128 as f64
        );
        assert_eq!(h64("0x0000000000000000000001p0"), 1.0);
        assert_eq!(h64("0x1p99999999999999999999"), f64::INFINITY);
        assert_eq!(h64("0x1p-99999999999999999999"), 0.0);
    }

    #[test]
    fn hexadecimal_rounding_is_direct() {
        // Ties go to even; a nonzero tail beyond the tie rounds up.
        assert_eq!(h32("0x1.000001p0"), 1.0);
        assert_eq!(h32("0x1.000003p0"), f32::from_bits(0x3f80_0002));
        assert_eq!(
            h32("0x1.0000010000000000000001p0"),
            f32::from_bits(0x3f80_0001)
        );
        assert_eq!(h32("0x1.fffffep127"), f32::MAX);
        assert_eq!(h32("0x1.ffffffp127"), f32::INFINITY);
        assert_eq!(h32("0x1p-149"), f32::from_bits(1));
        assert_eq!(h32("0x1p-150"), 0.0);
        // 1 + 2^-24 + 2^-60: rounding through f64 first gives a tie, and
        // then 1.0.
        assert_eq!(h32("0x1.000001000000001p0"), f32::from_bits(0x3f80_0001));
        assert_eq!(h64("0x1.000001000000001p0") as f32, 1.0);
    }

    #[test]
    fn decimal_values_round_directly_to_f32() {
        let direct = parse_f32(b"1.0000000596046448", false);
        assert_eq!(direct.to_bits(), 0x3f80_0001);
        let through_f64 = parse_f64(b"1.0000000596046448", false) as f32;
        assert_eq!(through_f64.to_bits(), 0x3f80_0000);
    }
}
