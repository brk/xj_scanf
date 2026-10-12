//! Behavior of the shared engine through the in-memory and reader front ends.

use std::io::{self, BufRead, Cursor, Read};

use xj_bytes::{CStrBuffer, CStrDest};
use xj_scanf::*;

/// Scans `input` (all bytes, NULs included) and returns the outcome and the
/// unread rest.
fn run<'a>(
    input: &'a [u8],
    format: &str,
    args: &mut [&mut dyn ScanTarget],
) -> (ScanOutcome, &'a [u8]) {
    let mut input = SliceInput::new(input);
    let outcome = vscan(&mut input, format.as_bytes(), &mut Targets::new(args));
    (outcome, input.rest())
}

fn ret(input: &str, format: &str, args: &mut [&mut dyn ScanTarget]) -> i32 {
    sscanf(input, format, args)
}

// ---------------------------------------------------------------------------
// Integers

#[test]
fn decimal_integers() {
    let (mut a, mut b, mut c) = (0i32, 0i32, 0i32);
    assert_eq!(ret("1 -2 +3", "%d %d %d", &mut [&mut a, &mut b, &mut c]), 3);
    assert_eq!((a, b, c), (1, -2, 3));
    // `%d` is always base 10.
    assert_eq!(ret("010", "%d", &mut [&mut a]), 1);
    assert_eq!(a, 10);
}

#[test]
fn bases_and_prefixes() {
    let mut x = 0u32;
    let mut i = 0i32;
    for (input, value) in [
        ("1a2b", 0x1a2b),
        ("0xDEAD", 0xdead),
        ("0X1f", 31),
        ("0", 0),
        ("ff", 255),
    ] {
        assert_eq!(ret(input, "%x", &mut [&mut x]), 1, "{input}");
        assert_eq!(x, value, "{input}");
    }
    assert_eq!(ret("755", "%o", &mut [&mut x]), 1);
    assert_eq!(x, 0o755);
    for (input, value) in [
        ("123", 123),
        ("0755", 0o755),
        ("0x1A", 26),
        ("-0x10", -16),
        ("08", 0),
    ] {
        assert_eq!(ret(input, "%i", &mut [&mut i]), 1, "{input}");
        assert_eq!(i, value, "{input}");
    }
}

#[test]
fn integer_items_end_at_the_right_byte() {
    let mut i = 0i32;
    let (o, rest) = run(b"12ab", "%i", &mut [&mut i]);
    assert_eq!((o.c_return(), i, rest), (1, 12, &b"ab"[..]));
    let (o, rest) = run(b"123abc", "%i", &mut [&mut i]);
    assert_eq!((o.c_return(), i, rest), (1, 123, &b"abc"[..]));
    let (o, rest) = run(b"08", "%i", &mut [&mut i]);
    assert_eq!((o.c_return(), i, rest), (1, 0, &b"8"[..]));
    let mut x = 0u32;
    let (o, rest) = run(b"0xff", "%x", &mut [&mut x]);
    assert_eq!((o.c_return(), x, rest), (1, 255, &b""[..]));
}

#[test]
fn incomplete_hex_prefix_is_a_matching_failure() {
    for format in ["%x", "%i"] {
        let mut x = 7u32;
        let (o, rest) = run(b"0xg", format, &mut [&mut x]);
        assert!(matches!(o.stop, Stop::MatchingFailure), "{format}");
        assert_eq!((o.c_return(), x, rest, o.consumed), (0, 7, &b"g"[..], 2));
    }
}

#[test]
fn widths_bound_signs_and_prefixes() {
    let mut x = 0u32;
    let mut d = 0i32;
    let (o, rest) = run(b"0x1", "%2x", &mut [&mut x]);
    assert!(matches!(o.stop, Stop::MatchingFailure));
    assert_eq!(rest, b"1");
    let (o, rest) = run(b"0x1", "%1x", &mut [&mut x]);
    assert_eq!((o.c_return(), x, rest), (1, 0, &b"x1"[..]));
    let (o, rest) = run(b"-5", "%1d", &mut [&mut d]);
    assert!(matches!(o.stop, Stop::MatchingFailure));
    assert_eq!(rest, b"5");
    let (o, rest) = run(b"12345", "%3d%d", &mut [&mut d, &mut x]);
    assert_eq!((o.c_return(), d, x, rest), (2, 123, 45, &b""[..]));
}

#[test]
fn length_modifiers_select_the_destination_width() {
    let (mut c, mut h, mut l, mut ll) = (0i8, 0i16, 0i64, 0i64);
    let (mut z, mut j, mut t) = (0usize, 0i64, 0isize);
    assert_eq!(
        ret(
            "-1 -2 -3 -4 5 -6 -7",
            "%hhd %hd %ld %lld %zu %jd %td",
            &mut [&mut c, &mut h, &mut l, &mut ll, &mut z, &mut j, &mut t]
        ),
        7
    );
    assert_eq!((c, h, l, ll, z, j, t), (-1, -2, -3, -4, 5, -6, -7));
    let (mut uc, mut uh) = (0u8, 0u16);
    assert_eq!(ret("255 65535", "%hhu %hu", &mut [&mut uc, &mut uh]), 2);
    assert_eq!((uc, uh), (255, 65535));
}

#[test]
fn overflow_saturates_silently() {
    let (mut a, mut b) = (0i32, 0i32);
    assert_eq!(
        ret("1 99999999999999999999", "%d %d", &mut [&mut a, &mut b]),
        2
    );
    assert_eq!((a, b), (1, i32::MAX));
    assert_eq!(
        ret("-99999999999999999999 4", "%d %d", &mut [&mut a, &mut b]),
        2
    );
    assert_eq!((a, b), (i32::MIN, 4));
    let (mut c, mut uc) = (0i8, 0u8);
    assert_eq!(ret("-128 -128", "%hhd %hhu", &mut [&mut c, &mut uc]), 2);
    assert_eq!((c, uc), (-128, 128));
    assert_eq!(ret("300 300", "%hhd %hhu", &mut [&mut c, &mut uc]), 2);
    assert_eq!((c, uc), (127, 255));
    assert_eq!(ret("-300", "%hhu", &mut [&mut uc]), 1);
    assert_eq!(uc, 255);
    let mut u = 0u32;
    assert_eq!(ret("-1", "%u", &mut [&mut u]), 1);
    assert_eq!(u, u32::MAX);
    assert_eq!(ret("4294967296", "%u", &mut [&mut u]), 1);
    assert_eq!(u, u32::MAX);
    let mut w = 0u64;
    assert_eq!(ret("18446744073709551615", "%llu", &mut [&mut w]), 1);
    assert_eq!(w, u64::MAX);
    assert_eq!(ret("-18446744073709551616", "%llu", &mut [&mut w]), 1);
    assert_eq!(w, u64::MAX);
    let mut s = 0i64;
    assert_eq!(ret("-9223372036854775808", "%lld", &mut [&mut s]), 1);
    assert_eq!(s, i64::MIN);
}

#[test]
fn signedness_follows_the_destination() {
    let mut s = 0i32;
    let mut u = 0u32;
    assert_eq!(ret("-1 4294967295", "%u %d", &mut [&mut s, &mut u]), 2);
    assert_eq!((s, u), (-1, u32::MAX));
    // An unsigned directive's in-range value keeps its bit pattern.
    let mut c = 0i8;
    assert_eq!(ret("4294967295 255", "%u %hhu", &mut [&mut s, &mut c]), 2);
    assert_eq!((s, c), (-1, -1));
    // Out of range for both types: saturate by the destination.
    assert_eq!(
        ret("-5000000000 99999999999", "%u %d", &mut [&mut s, &mut u]),
        2
    );
    assert_eq!((s, u), (i32::MIN, u32::MAX));
}

// ---------------------------------------------------------------------------
// Floats

#[test]
fn decimal_floats() {
    let (mut f, mut d) = (0f32, 0f64);
    assert_eq!(ret("3.25 -1.5e2", "%f %lf", &mut [&mut f, &mut d]), 2);
    assert_eq!((f, d), (3.25, -150.0));
    for (input, value) in [("1.", 1.0), (".5", 0.5), ("+2E+1", 20.0), ("7", 7.0)] {
        assert_eq!(ret(input, "%lg", &mut [&mut d]), 1, "{input}");
        assert_eq!(d, value, "{input}");
    }
}

#[test]
fn every_floating_directive_accepts_every_form() {
    for format in ["%le", "%lE", "%lf", "%lF", "%lg", "%lG", "%la", "%lA"] {
        for (input, value) in [
            ("0x1.8p1", 3.0),
            ("1e1", 10.0),
            ("-INF", f64::NEG_INFINITY),
            ("infinity", f64::INFINITY),
        ] {
            let mut d = 0f64;
            assert_eq!(ret(input, format, &mut [&mut d]), 1, "{format} {input}");
            assert_eq!(d, value, "{format} {input}");
        }
        let mut d = 0f64;
        assert_eq!(ret("nan(123abc_)x", format, &mut [&mut d]), 1);
        assert!(d.is_nan());
        assert_eq!(ret("-NaN", format, &mut [&mut d]), 1);
        assert!(d.is_nan() && d.is_sign_negative());
    }
}

#[test]
fn float_items_follow_the_longest_prefix_rule() {
    let mut f = 9f32;
    for (input, rest) in [
        (&b"100er"[..], &b"r"[..]),
        (b"1e+x", b"x"),
        (b"0x", b""),
        (b"0xg", b"g"),
        (b".x", b"x"),
        (b"-", b""),
        (b"infin", b""),
        (b"infinit!", b"!"),
        (b"nan(ab", b""),
        (b"nan(a b)", b" b)"),
        (b"0x1p", b""),
    ] {
        let (o, unread) = run(input, "%f", &mut [&mut f]);
        assert!(matches!(o.stop, Stop::MatchingFailure), "{input:?}: {o:?}");
        assert_eq!((o.c_return(), f, unread), (0, 9.0, rest), "{input:?}");
    }
    let (o, unread) = run(b"infx", "%f", &mut [&mut f]);
    assert_eq!((o.c_return(), f, unread), (1, f32::INFINITY, &b"x"[..]));
    let (o, unread) = run(b"1.5e3x", "%4f", &mut [&mut f]);
    assert_eq!((o.c_return(), f, unread), (0, f32::INFINITY, &b"3x"[..]));
    let (o, unread) = run(b"1.5e3x", "%5f", &mut [&mut f]);
    assert_eq!((o.c_return(), f, unread), (1, 1500.0, &b"x"[..]));
}

#[test]
fn float_precision_is_direct() {
    let (mut f, mut d) = (0f32, 0f64);
    assert_eq!(ret("1.0000000596046448", "%f", &mut [&mut f]), 1);
    assert_eq!(f.to_bits(), 0x3f80_0001);
    assert_eq!(ret("0x1.000001000000001p0", "%a", &mut [&mut f]), 1);
    assert_eq!(f.to_bits(), 0x3f80_0001);
    assert_eq!(ret("0.1", "%lf", &mut [&mut d]), 1);
    assert_eq!(d, 0.1);
}

#[test]
fn long_float_fields_are_never_truncated() {
    let digits = "1".repeat(400);
    let input = format!("0.{digits}e400 next");
    let mut d = 0f64;
    let mut word = String::new();
    assert_eq!(ret(&input, "%lf %s", &mut [&mut d, &mut word]), 2);
    assert_eq!(d, format!("0.{digits}e400").parse::<f64>().unwrap());
    assert_eq!(word, "next");
}

// ---------------------------------------------------------------------------
// Bytes

#[test]
fn strings_and_sets() {
    let mut s = String::new();
    let mut v = Vec::new();
    assert_eq!(ret("  hello world", "%s %s", &mut [&mut s, &mut v]), 2);
    assert_eq!((s.as_str(), &v[..]), ("hello", &b"world"[..]));
    assert_eq!(ret("verylongword", "%5s", &mut [&mut s]), 1);
    assert_eq!(s, "veryl");
    assert_eq!(ret("abc123", "%[a-z]", &mut [&mut s]), 1);
    assert_eq!(s, "abc");
    assert_eq!(ret("abc:def", "%[^:]", &mut [&mut s]), 1);
    assert_eq!(s, "abc");
    assert_eq!(ret("ab12 ", "%4[a-z0-9] ", &mut [&mut s]), 1);
    assert_eq!(s, "ab12");
    assert_eq!(ret("ab12 ", "%5[a-z0-9] ", &mut [&mut s]), 1);
    assert_eq!(s, "ab12");
    // managarm/mlibc#1496
    assert_eq!(ret("zz-zxx-mmm ", "%7[zx-]", &mut [&mut s]), 1);
    assert_eq!(s, "zz-zxx-");
    // `%[` does not skip whitespace.
    let (o, rest) = run(b" abc", "%[a-z]", &mut [&mut s]);
    assert!(matches!(o.stop, Stop::MatchingFailure));
    assert_eq!(rest, b" abc");
}

#[test]
fn chars() {
    let mut v = Vec::new();
    assert_eq!(ret(" xxx", "%3c", &mut [&mut v]), 1);
    assert_eq!(v, b" xx");
    let mut c = 0u8;
    let mut i = 0i8;
    assert_eq!(ret("AB", "%c%c", &mut [&mut c, &mut i]), 2);
    assert_eq!((c, i), (b'A', b'B' as i8));
    let mut buf = [b'_'; 6];
    assert_eq!(ret("ABCDEF", "%3c", &mut [&mut buf]), 1);
    assert_eq!(&buf, b"ABC___");
    // A short `%Nc` field is an incomplete item: nothing is stored.
    let mut buf = [b'_'; 4];
    let (o, rest) = run(b"ab", "%3c", &mut [&mut buf]);
    assert!(matches!(o.stop, Stop::MatchingFailure));
    assert_eq!((o.c_return(), &buf, rest), (0, b"____", &b""[..]));
}

#[test]
fn bytes_are_not_re_encoded() {
    let mut v = Vec::new();
    assert_eq!(bscanf(b"\xe9t\xe9 \xff", "%s", &mut [&mut v]), 1);
    assert_eq!(v, b"\xe9t\xe9");
    let mut s = String::from("unchanged");
    let (o, _) = run(b"\xff", "%s", &mut [&mut s]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            index: 0,
            err: StoreError::TypeMismatch
        }
    ));
    assert_eq!((o.c_return(), s.as_str()), (0, "unchanged"));
    // Format bytes need not be UTF-8 either.
    let mut x = 0i32;
    assert_eq!(bscanf(b"\xfe5", b"\xfe%d", &mut [&mut x]), 1);
    assert_eq!(x, 5);
}

#[test]
fn bounded_destinations_never_overflow() {
    // Exact fit.
    let mut word = [b'_'; 6];
    assert_eq!(ret("hello", "%s", &mut [&mut word]), 1);
    assert_eq!(&word, b"hello\0");
    // Overflow: the prefix that fits, terminated, and the rest unread.
    let mut word = [b'_'; 4];
    let mut n = 0i32;
    let (o, rest) = run(b"abcdefg 5", "%s %d", &mut [&mut word, &mut n]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            index: 0,
            err: StoreError::Capacity
        }
    ));
    assert_eq!(
        (o.c_return(), &word, rest, n),
        (0, b"abc\0", &b"defg 5"[..], 0)
    );
    // A width smaller than the destination ends the field first.
    let mut word = [b'_'; 8];
    let (o, rest) = run(b"abcdefg", "%3s", &mut [&mut word]);
    assert_eq!(
        (o.c_return(), &word[..4], rest),
        (1, &b"abc\0"[..], &b"defg"[..])
    );
    // A field that fits after a width cut is not an overflow.
    let mut word = [b'_'; 4];
    let (o, rest) = run(b"abcdefg", "%3s", &mut [&mut word]);
    assert_eq!((o.c_return(), &word, rest), (1, b"abc\0", &b"defg"[..]));
    // Zero and one byte of capacity.
    let mut empty: [u8; 0] = [];
    let (o, rest) = run(b"x", "%s", &mut [&mut empty]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            err: StoreError::Capacity,
            ..
        }
    ));
    assert_eq!(rest, b"x");
    let mut one = [b'_'; 1];
    let (o, rest) = run(b"x", "%s", &mut [&mut one]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            err: StoreError::Capacity,
            ..
        }
    ));
    assert_eq!((one, rest), ([0], &b"x"[..]));
    let (o, _) = run(b"", "%s", &mut [&mut empty]);
    assert!(matches!(o.stop, Stop::InputEnd));
    // `%Nc` rejects insufficient room before reading.
    let mut small = [b'_'; 2];
    let (o, rest) = run(b"abc", "%3c", &mut [&mut small]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            err: StoreError::Capacity,
            ..
        }
    ));
    assert_eq!((small, rest, o.consumed), (*b"__", &b"abc"[..], 0));
}

#[test]
fn shared_destination_views() {
    // A protected final NUL is never written.
    let mut storage = *b"xxxx\0";
    let mut dest = CStrDest::with_reserved_nul(&mut storage);
    assert_eq!(ret("abcd", "%s", &mut [&mut dest]), 1);
    assert_eq!(&storage, b"abcd\0");
    let mut storage = *b"xxxx\0";
    let mut dest = CStrDest::with_reserved_nul(&mut storage);
    let (o, _) = run(b"abcde", "%5c", &mut [&mut dest]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            err: StoreError::Capacity,
            ..
        }
    ));
    assert_eq!(&storage, b"xxxx\0");
    let mut dest = CStrDest::with_reserved_nul(&mut storage);
    assert_eq!(ret("abcd", "%4c", &mut [&mut dest]), 1);
    assert_eq!(&storage, b"abcd\0");
    // A limited view.
    let mut buf = *b"________";
    let mut limited = buf.cstr_dest().limit(3);
    let (o, rest) = run(b"abcdef", "%s", &mut [&mut limited]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            err: StoreError::Capacity,
            ..
        }
    ));
    assert_eq!((&buf, rest), (b"ab\0_____", &b"cdef"[..]));
    // A vector's slice is bounded; the vector itself grows.
    let mut vec = vec![b'_'; 3];
    let (o, _) = run(b"abcdef", "%s", &mut [&mut vec.as_mut_slice()]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            err: StoreError::Capacity,
            ..
        }
    ));
    assert_eq!(vec, b"ab\0");
    assert_eq!(ret("abcdef", "%s", &mut [&mut vec]), 1);
    assert_eq!(vec, b"abcdef");
}

// ---------------------------------------------------------------------------
// Outcomes

#[test]
fn standard_outcomes() {
    let mut x = 5i32;
    let mut n = 9i32;
    // A literal match is not an input conversion.
    assert_eq!(ret("x", "x%d", &mut [&mut x]), -1);
    // `%n` stores zero, then EOF.
    let (o, _) = run(b"", "%n%d", &mut [&mut n, &mut x]);
    assert_eq!((o.c_return(), n, x), (-1, 0, 5));
    // A suppressed input conversion completed.
    assert_eq!(ret("1", "%*d%d", &mut [&mut x]), 0);
    assert_eq!(ret("1", "%*d", &mut []), 0);
    n = 9;
    let (o, _) = run(b"", " %n", &mut [&mut n]);
    assert!(matches!(o.stop, Stop::FormatEnd));
    assert_eq!((o.c_return(), n), (0, 0));
    // Empty or blank input before the first conversion.
    assert_eq!(ret("", "%d", &mut [&mut x]), -1);
    assert_eq!(ret("   ", "%d", &mut [&mut x]), -1);
    assert_eq!(ret("", " %d", &mut [&mut x]), -1);
    assert_eq!(ret("", "a", &mut []), -1);
    assert_eq!(ret("abc", "%d", &mut [&mut x]), 0);
    // Partial success, then a matching failure or EOF.
    let (mut a, mut b) = (0i32, 0i32);
    assert_eq!(ret("42 abc", "%d %d", &mut [&mut a, &mut b]), 1);
    assert_eq!(a, 42);
    assert_eq!(ret("1 ", "%d %s", &mut [&mut a, &mut String::new()]), 1);
    assert_eq!(ret("42", "%d %s", &mut [&mut a, &mut String::new()]), 1);
    assert_eq!(ret("%42", "%%%d", &mut [&mut a]), 1);
    assert_eq!(ret(" %", " %%", &mut []), 0);
    assert_eq!(ret("0", "%f%c", &mut [&mut 0f32, &mut 0u8]), 1);
}

#[test]
fn count_stores_into_any_integer_of_its_width() {
    let (mut x, mut n, mut l, mut z) = (0i32, 0u32, 0i64, 0usize);
    let (o, _) = run(
        b"123 ab",
        "%d%n %*s%ln%zn",
        &mut [&mut x, &mut n, &mut l, &mut z],
    );
    assert_eq!((o.c_return(), o.assigned, x, n, l, z), (1, 1, 123, 3, 6, 6));
    let mut c = 0i8;
    assert_eq!(ret("abc", "%*s%hhn", &mut [&mut c]), 0);
    assert_eq!(c, 3);
    let (o, _) = run(b"abc", "%*s%hhn", &mut [&mut x]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            index: 0,
            err: StoreError::TypeMismatch
        }
    ));
}

#[test]
fn destinations_are_checked_before_input_is_consumed() {
    let mut short = 0i16;
    let mut x = 0i32;
    let mut y = 0i32;
    let mut d = 0f64;
    let mut f = 0f32;
    for (format, target) in [
        ("%d", &mut short as &mut dyn ScanTarget),
        ("%f", &mut d),
        ("%lf", &mut f),
        ("%s", &mut x),
        ("%d", &mut String::new()),
        ("%2c", &mut 0u8),
        ("%ld", &mut y),
    ] {
        let (o, rest) = run(b"  12", format, &mut [target]);
        assert!(
            matches!(
                o.stop,
                Stop::Store {
                    index: 0,
                    err: StoreError::TypeMismatch
                }
            ),
            "{format}: {o:?}"
        );
        assert_eq!(
            (o.c_return(), rest, o.consumed),
            (0, &b"  12"[..], 0),
            "{format}"
        );
    }
    let (o, rest) = run(b"1 2", "%d %d", &mut [&mut x]);
    assert!(matches!(
        o.stop,
        Stop::Store {
            index: 1,
            err: StoreError::Missing
        }
    ));
    assert_eq!((o.c_return(), rest), (1, &b"2"[..]));
    // Accepted: signedness and equal-width rank differences.
    let mut u = 0u32;
    let mut s = 0usize;
    assert_eq!(ret("7 8", "%d %lu", &mut [&mut u, &mut s]), 2);
    assert_eq!((u, s), (7, 8));
}

#[test]
fn invalid_formats_are_rejected_before_reading() {
    let mut x = 0i32;
    for (format, offset) in [
        ("%d %p", 3),
        ("%Lf", 0),
        ("%lc", 0),
        ("%ls", 0),
        ("ab%y", 2),
        ("%", 0),
    ] {
        let (o, rest) = run(b"12", format, &mut [&mut x]);
        assert!(
            matches!(o.stop, Stop::InvalidFormat { offset: at } if at == offset),
            "{format}: {o:?}"
        );
        assert_eq!((o.c_return(), x, rest), (0, 0, &b"12"[..]), "{format}");
    }
}

#[test]
fn c_string_input_stops_at_nul_but_readers_do_not() {
    let (mut a, mut b) = (0i32, 0i32);
    assert_eq!(sscanf(b"1\x002", "%d%d", &mut [&mut a, &mut b]), 1);
    assert_eq!(sscanf(c"3 4", "%d%d", &mut [&mut a, &mut b]), 2);
    assert_eq!((a, b), (3, 4));
    assert_eq!(sscanf("5 6", "%d\0%d", &mut [&mut a, &mut b]), 1);
    assert_eq!(a, 5);
    let mut c = 9u8;
    assert_eq!(
        brscanf(&b"1\x002"[..], "%d%c%d", &mut [&mut a, &mut c, &mut b]),
        3
    );
    assert_eq!((a, c, b), (1, 0, 2));
}

#[test]
fn repeated_reader_calls_see_consistent_data() {
    let mut reader = Cursor::new(&b"12Xrest 34"[..]);
    let mut x = 0i32;
    assert_eq!(brscanf(&mut reader, "%dY", &mut [&mut x]), 1);
    let mut rest = String::new();
    reader.read_to_string(&mut rest).unwrap();
    assert_eq!(rest, "Xrest 34");
    let mut reader = Cursor::new(&b"1 2 3"[..]);
    let mut v = [0i32; 3];
    for slot in &mut v {
        assert_eq!(brscanf(&mut reader, "%d", &mut [slot]), 1);
    }
    assert_eq!(v, [1, 2, 3]);
}

/// A reader that yields its bytes and then fails.
struct Failing(&'static [u8]);

impl io::Read for Failing {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        unreachable!()
    }
}

impl BufRead for Failing {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.0.is_empty() {
            Err(io::Error::other("injected"))
        } else {
            Ok(&self.0[..1])
        }
    }

    fn consume(&mut self, n: usize) {
        self.0 = &self.0[n..];
    }
}

#[test]
fn read_errors_are_not_matching_failures() {
    let mut x = 0i32;
    let mut input = ReadInput(Failing(b""));
    let o = vscan(&mut input, b"%d", &mut Targets::new(&mut [&mut x]));
    assert!(matches!(o.stop, Stop::Io(_)));
    assert_eq!(o.c_return(), -1);
    // A read error ends a valid item as end of input does; the next
    // directive then fails with the error.
    let (mut a, mut b) = (0i32, 0i32);
    let mut input = ReadInput(Failing(b"12"));
    let o = vscan(
        &mut input,
        b"%d %d",
        &mut Targets::new(&mut [&mut a, &mut b]),
    );
    assert!(matches!(o.stop, Stop::Io(_)), "{o:?}");
    assert_eq!((o.c_return(), a), (1, 12));
}

#[test]
fn macros() {
    let (mut a, mut b) = (0i32, 0f32);
    assert_eq!(sscanf!("10 2.5", "%d %f", &mut a, &mut b), 2);
    assert_eq!((a, b), (10, 2.5));
    assert_eq!(sscanf!("%%", "%%%%"), 0);
    assert_eq!(bscanf!(b"7", "%d", &mut a), 1);
    assert_eq!(brscanf!(Cursor::new("8"), "%d", &mut a), 1);
    assert_eq!(a, 8);
    assert_eq!(brscanf!(Cursor::new("%%"), "%%%%"), 0);
}

#[test]
fn mixed_numeric_regression() {
    let input = "4\n-2-2.0211.968\n0\n0\n0\n07\n2.0.0\n8\n86";
    let mut i = [0i32; 6];
    let mut f = [0f32; 6];
    let [i0, i1, i2, i3, i4, i5] = &mut i;
    let [f0, f1, f2, f3, f4, f5] = &mut f;
    assert_eq!(
        sscanf!(
            input,
            "%d%f%f%f%d%d%d%d%f%f%f%d",
            i0,
            f0,
            f1,
            f2,
            i1,
            i2,
            i3,
            i4,
            f3,
            f4,
            f5,
            i5
        ),
        12
    );
    assert_eq!(i, [4, 0, 0, 0, 7, 86]);
    assert_eq!(f, [-2.0, -2.0211, 0.968, 2.0, 0.0, 8.0]);
}
