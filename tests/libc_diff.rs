//! Differential tests against the host libc, for defined inputs.
//!
//! Each case runs through `fmemopen` + `fscanf` and through the engine's
//! slice adapter, with destinations chosen from the format's requirements,
//! and compares the return value, every destination's bytes and the next
//! unread byte. Cases where libc disagrees with the standard are listed in
//! `LIBC_DIFFERS` and asserted directly in `tests/engine.rs` instead.
#![cfg(target_os = "linux")]

use std::ffi::{CString, c_void};

use xj_scanf::xj_scanf_core::{Format, IntKind, Requirement};
use xj_scanf::*;

mod cases;
use cases::{CASES, LIBC_DIFFERS};

#[derive(Clone, Copy)]
enum Dest {
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Bytes,
}

fn dests(format: &str) -> Vec<Dest> {
    Format::requirements(format.as_bytes())
        .map(|r| match r.unwrap() {
            Requirement::Int { kind, .. } | Requirement::Count(kind) => match kind {
                IntKind::Char => Dest::I8,
                IntKind::Short => Dest::I16,
                IntKind::Int => Dest::I32,
                _ => Dest::I64,
            },
            Requirement::Float => Dest::F32,
            Requirement::Double => Dest::F64,
            Requirement::Str | Requirement::Chars(_) => Dest::Bytes,
        })
        .collect()
}

/// Storage for one destination, prefilled with a sentinel.
struct Slot {
    dest: Dest,
    bytes: [u8; 32],
}

impl Slot {
    fn new(dest: Dest) -> Self {
        Slot {
            dest,
            bytes: [0xa5; 32],
        }
    }

    fn ptr(&mut self) -> *mut c_void {
        self.bytes.as_mut_ptr().cast()
    }

    fn compared(&self) -> &[u8] {
        let n = match self.dest {
            Dest::I8 => 1,
            Dest::I16 => 2,
            Dest::I32 | Dest::F32 => 4,
            Dest::I64 | Dest::F64 => 8,
            Dest::Bytes => 32,
        };
        &self.bytes[..n]
    }
}

fn libc_scan(input: &[u8], format: &str, slots: &mut [Slot]) -> (i32, Option<u8>) {
    let fmt = CString::new(format).unwrap();
    let mut owned = input.to_vec();
    owned.push(0);
    unsafe {
        let f = libc::fmemopen(owned.as_mut_ptr().cast(), input.len(), c"r".as_ptr());
        assert!(!f.is_null());
        let p: Vec<_> = slots.iter_mut().map(Slot::ptr).collect();
        let fmt = fmt.as_ptr();
        let r = match p[..] {
            [] => libc::fscanf(f, fmt),
            [a] => libc::fscanf(f, fmt, a),
            [a, b] => libc::fscanf(f, fmt, a, b),
            [a, b, c] => libc::fscanf(f, fmt, a, b, c),
            [a, b, c, d] => libc::fscanf(f, fmt, a, b, c, d),
            _ => panic!("too many destinations"),
        };
        let next = libc::fgetc(f);
        libc::fclose(f);
        (r, u8::try_from(next).ok())
    }
}

fn engine_scan(input: &[u8], format: &str, slots: &mut [Slot]) -> (i32, Option<u8>) {
    let sentinel = |n: usize| -> [u8; 8] { std::array::from_fn(|i| if i < n { 0xa5 } else { 0 }) };
    let mut i8s: Vec<i8> = Vec::new();
    let mut i16s: Vec<i16> = Vec::new();
    let mut i32s: Vec<i32> = Vec::new();
    let mut i64s: Vec<i64> = Vec::new();
    let mut f32s: Vec<f32> = Vec::new();
    let mut f64s: Vec<f64> = Vec::new();
    for slot in slots.iter() {
        let s = sentinel(8);
        match slot.dest {
            Dest::I8 => i8s.push(s[0] as i8),
            Dest::I16 => i16s.push(i16::from_ne_bytes([s[0], s[1]])),
            Dest::I32 => i32s.push(i32::from_ne_bytes(s[..4].try_into().unwrap())),
            Dest::I64 => i64s.push(i64::from_ne_bytes(s)),
            Dest::F32 => f32s.push(f32::from_ne_bytes(s[..4].try_into().unwrap())),
            Dest::F64 => f64s.push(f64::from_ne_bytes(s)),
            Dest::Bytes => {}
        }
    }
    let (mut i8s, mut i16s, mut i32s, mut i64s, mut f32s, mut f64s) = (
        i8s.iter_mut(),
        i16s.iter_mut(),
        i32s.iter_mut(),
        i64s.iter_mut(),
        f32s.iter_mut(),
        f64s.iter_mut(),
    );
    let mut targets: Vec<&mut dyn ScanTarget> = Vec::new();
    let mut typed: Vec<(usize, *const u8, usize)> = Vec::new();
    for (index, slot) in slots.iter_mut().enumerate() {
        let (dest, len) = (slot.dest, slot.compared().len());
        let target: &mut dyn ScanTarget = match dest {
            Dest::I8 => i8s.next().unwrap(),
            Dest::I16 => i16s.next().unwrap(),
            Dest::I32 => i32s.next().unwrap(),
            Dest::I64 => i64s.next().unwrap(),
            Dest::F32 => f32s.next().unwrap(),
            Dest::F64 => f64s.next().unwrap(),
            Dest::Bytes => &mut slot.bytes,
        };
        if !matches!(dest, Dest::Bytes) {
            typed.push((index, (target as *mut dyn ScanTarget).cast::<u8>(), len));
        }
        targets.push(target);
    }
    let mut cursor = SliceInput::new(input);
    let outcome = vscan(
        &mut cursor,
        format.as_bytes(),
        &mut Targets::new(&mut targets),
    );
    drop(targets);
    for (index, ptr, len) in typed {
        // SAFETY: `ptr` addresses a live, initialized integer or float of
        // `len` bytes in one of the vectors above, which are no longer
        // mutably borrowed.
        let value = unsafe { std::slice::from_raw_parts(ptr, len) };
        slots[index].bytes[..len].copy_from_slice(value);
    }
    (outcome.c_return(), cursor.rest().first().copied())
}

fn check(input: &[u8], format: &str) -> Option<String> {
    let kinds = dests(format);
    let mut ours: Vec<Slot> = kinds.iter().map(|&d| Slot::new(d)).collect();
    let mut theirs: Vec<Slot> = kinds.iter().map(|&d| Slot::new(d)).collect();
    let a = engine_scan(input, format, &mut ours);
    let b = libc_scan(input, format, &mut theirs);
    let ours_bytes: Vec<&[u8]> = ours.iter().map(Slot::compared).collect();
    let theirs_bytes: Vec<&[u8]> = theirs.iter().map(Slot::compared).collect();
    (a != b || ours_bytes != theirs_bytes).then(|| {
        format!(
            "{:?} {format:?}: engine {a:?} {ours_bytes:?}, libc {b:?} {theirs_bytes:?}",
            String::from_utf8_lossy(input)
        )
    })
}

#[test]
fn defined_inputs_match_libc() {
    let failures: Vec<String> = CASES.iter().filter_map(|&(i, f)| check(i, f)).collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn recorded_libc_differences_still_differ() {
    // If glibc starts agreeing with the standard, drop the entry.
    for &(input, format) in LIBC_DIFFERS {
        assert!(
            check(input, format).is_some(),
            "{input:?} {format:?} now matches libc"
        );
    }
}
