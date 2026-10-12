//! The scanning engine: format items against a [`ScanInput`], storing into
//! [`ScanArgs`] destinations in order.

use std::io;

use crate::float;
use crate::{ScanArgs, ScanInput, ScanOutcome, Stop, StoreError, Value};
use xj_scanf_core::{Conv, Format, Item, LengthMod, is_space};

/// Why an input item failed.
enum Fail {
    /// The item was empty because input ended (or a read failed).
    Input,
    /// The item was not a matching sequence.
    Matching,
}

pub(crate) struct Scanner<'i, I: ScanInput + ?Sized> {
    input: &'i mut I,
    /// Bytes consumed in this call.
    consumed: usize,
    /// Input ended (or failed) during this call. Like C's EOF indicator,
    /// this is sticky: later peeks return `None` without reading again.
    ended: bool,
    error: Option<io::Error>,
    /// Field and token bytes, for inputs that do not retain them.
    buf: Vec<u8>,
}

impl<I: ScanInput + ?Sized> Scanner<'_, I> {
    fn peek(&mut self) -> Option<u8> {
        if self.ended {
            return None;
        }
        match self.input.peek() {
            Ok(Some(byte)) => Some(byte),
            Ok(None) => {
                self.ended = true;
                None
            }
            Err(e) => {
                // A read error ends the input item, as end of input does.
                self.ended = true;
                self.error = Some(e);
                None
            }
        }
    }

    /// Consumes the byte returned by the last `peek`.
    fn bump(&mut self) {
        self.input.bump();
        self.consumed += 1;
    }

    fn skip_space(&mut self) {
        while self.peek().is_some_and(is_space) {
            self.bump();
        }
    }

    /// The next byte, if it is within `n < width` and satisfies `accept`.
    fn next_if(&mut self, n: usize, width: usize, accept: impl FnOnce(u8) -> bool) -> Option<u8> {
        if n >= width {
            return None;
        }
        self.peek().filter(|&b| accept(b))
    }

    fn input_failure(&mut self) -> Stop {
        match self.error.take() {
            Some(e) => Stop::Io(e),
            None => Stop::InputEnd,
        }
    }

    fn empty_item(&self) -> Fail {
        if self.ended {
            Fail::Input
        } else {
            Fail::Matching
        }
    }

    /// A strtol-style integer item, bounded by `width`. Returns the sign,
    /// the magnitude and whether the magnitude overflowed `u64`.
    fn int(&mut self, base: u8, width: usize) -> Result<Value<'static>, Fail> {
        let mut n = 0;
        let mut neg = false;
        if let Some(sign) = self.next_if(n, width, |b| b == b'+' || b == b'-') {
            self.bump();
            n += 1;
            neg = sign == b'-';
        }
        let mut base = u32::from(base);
        let mut digits = 0usize;
        if (base == 16 || base == 0) && self.next_if(n, width, |b| b == b'0').is_some() {
            self.bump();
            n += 1;
            digits = 1;
            if self.next_if(n, width, |b| b == b'x' || b == b'X').is_some() {
                // `0x` must be followed by a hexadecimal digit. Without one
                // it is an incomplete item, not zero.
                self.bump();
                n += 1;
                base = 16;
                digits = 0;
            } else if base == 0 {
                base = 8;
            }
        } else if base == 0 {
            base = 10;
        }
        let mut mag = 0u64;
        let mut overflow = false;
        while let Some(byte) = self.next_if(n, width, |b| (b as char).is_digit(base)) {
            self.bump();
            n += 1;
            digits += 1;
            let digit = u64::from((byte as char).to_digit(base).unwrap());
            match mag
                .checked_mul(u64::from(base))
                .and_then(|m| m.checked_add(digit))
            {
                Some(m) => mag = m,
                None => overflow = true,
            }
        }
        if digits == 0 {
            return Err(if n == 0 {
                self.empty_item()
            } else {
                Fail::Matching
            });
        }
        Ok(Value::Int {
            neg,
            mag: if overflow { u64::MAX } else { mag },
            overflow,
        })
    }

    /// A floating item of the strtod grammar (decimal, hexadecimal,
    /// infinity or NaN), bounded by `width` and converted directly to the
    /// destination precision.
    fn float(&mut self, width: usize, double: bool) -> Result<Value<'static>, Fail> {
        // The item so far is in `self.buf`, so its length bounds the width.
        self.buf.clear();
        macro_rules! take {
            ($byte:expr) => {{
                self.buf.push($byte);
                self.bump();
            }};
        }
        if let Some(sign) = self.next_if(self.buf.len(), width, |b| b == b'+' || b == b'-') {
            take!(sign);
        }
        let neg = self.buf.first() == Some(&b'-');
        if let Some(first) =
            self.next_if(self.buf.len(), width, |b| matches!(b | 0x20, b'i' | b'n'))
        {
            let word: &[u8] = if first | 0x20 == b'i' {
                b"infinity"
            } else {
                b"nan"
            };
            let mut k = 0;
            while k < word.len() {
                let Some(byte) = self.next_if(self.buf.len(), width, |b| b | 0x20 == word[k])
                else {
                    break;
                };
                take!(byte);
                k += 1;
            }
            let value = if word[0] == b'i' {
                if k != 3 && k != 8 {
                    return Err(Fail::Matching);
                }
                f64::INFINITY
            } else {
                if k != 3 {
                    return Err(Fail::Matching);
                }
                if self.next_if(self.buf.len(), width, |b| b == b'(').is_some() {
                    take!(b'(');
                    while let Some(byte) = self.next_if(self.buf.len(), width, |b| {
                        b.is_ascii_alphanumeric() || b == b'_'
                    }) {
                        take!(byte);
                    }
                    if self.next_if(self.buf.len(), width, |b| b == b')').is_none() {
                        return Err(Fail::Matching);
                    }
                    take!(b')');
                }
                // NaN payloads are not interpreted; the result is the
                // default quiet NaN with the input's sign.
                f64::NAN
            };
            let value = if neg { -value } else { value };
            return Ok(if double {
                Value::Float64(value)
            } else {
                Value::Float32(value as f32)
            });
        }
        let mut hex = false;
        let mut digits = 0usize;
        if self.next_if(self.buf.len(), width, |b| b == b'0').is_some() {
            take!(b'0');
            digits = 1;
            if let Some(x) = self.next_if(self.buf.len(), width, |b| b | 0x20 == b'x') {
                take!(x);
                hex = true;
                digits = 0;
            }
        }
        let is_digit = |b: u8| {
            if hex {
                b.is_ascii_hexdigit()
            } else {
                b.is_ascii_digit()
            }
        };
        while let Some(byte) = self.next_if(self.buf.len(), width, is_digit) {
            take!(byte);
            digits += 1;
        }
        if self.next_if(self.buf.len(), width, |b| b == b'.').is_some() {
            take!(b'.');
            while let Some(byte) = self.next_if(self.buf.len(), width, is_digit) {
                take!(byte);
                digits += 1;
            }
        }
        if digits == 0 {
            return Err(if self.buf.is_empty() {
                self.empty_item()
            } else {
                Fail::Matching
            });
        }
        let marker = if hex { b'p' } else { b'e' };
        if let Some(e) = self.next_if(self.buf.len(), width, |b| b | 0x20 == marker) {
            take!(e);
            if let Some(sign) = self.next_if(self.buf.len(), width, |b| b == b'+' || b == b'-') {
                take!(sign);
            }
            let mut exponent_digits = 0;
            while let Some(byte) = self.next_if(self.buf.len(), width, |b| b.is_ascii_digit()) {
                take!(byte);
                exponent_digits += 1;
            }
            if exponent_digits == 0 {
                return Err(Fail::Matching);
            }
        }
        let token = &self.buf[..];
        Ok(if double {
            Value::Float64(float::parse_f64(token, hex))
        } else {
            Value::Float32(float::parse_f32(token, hex))
        })
    }

    /// Collects up to `max` bytes accepted by `accept`. Returns the field
    /// length; the bytes are in `self.buf` unless the input retains them.
    fn field(&mut self, max: usize, retained: bool, accept: impl Fn(u8) -> bool) -> usize {
        self.buf.clear();
        let mut n = 0;
        while let Some(byte) = self.next_if(n, max, &accept) {
            if !retained {
                self.buf.push(byte);
            }
            self.bump();
            n += 1;
        }
        n
    }

    fn field_bytes(&self, n: usize, retained: bool) -> &[u8] {
        if retained {
            self.input.recent(n).expect("input retained its bytes")
        } else {
            &self.buf
        }
    }
}

/// Runs `format` against `input`, storing into `args` in order.
///
/// The format is read through its first NUL or end, and is validated before
/// any input is read or any destination claimed. Each conversion is stored
/// as soon as it succeeds; a later failure never undoes earlier stores.
pub fn vscan<I: ScanInput + ?Sized, A: ScanArgs + ?Sized>(
    input: &mut I,
    format: &[u8],
    args: &mut A,
) -> ScanOutcome {
    let mut s = Scanner {
        input,
        consumed: 0,
        ended: false,
        error: None,
        buf: Vec::new(),
    };
    let mut assigned = 0;
    let mut any_input = false;
    let stop = match Format::validate(format) {
        Err(e) => Stop::InvalidFormat { offset: e.offset },
        Ok(()) => run(&mut s, format, args, &mut assigned, &mut any_input),
    };
    ScanOutcome {
        assigned,
        any_input,
        consumed: s.consumed,
        stop,
    }
}

fn run<I: ScanInput + ?Sized, A: ScanArgs + ?Sized>(
    s: &mut Scanner<'_, I>,
    format: &[u8],
    args: &mut A,
    assigned: &mut usize,
    any_input: &mut bool,
) -> Stop {
    let mut claimed = 0;
    for item in Format::new(format) {
        let (_, item) = item.expect("validated format");
        let d = match item {
            Item::Space => {
                s.skip_space();
                continue;
            }
            Item::Byte(expected) => match s.peek() {
                Some(byte) if byte == expected => {
                    s.bump();
                    continue;
                }
                Some(_) => return Stop::MatchingFailure,
                None => return s.input_failure(),
            },
            Item::Directive(d) => d,
        };
        if d.conv == Conv::Percent {
            s.skip_space();
            match s.peek() {
                Some(b'%') => s.bump(),
                Some(_) => return Stop::MatchingFailure,
                None => return s.input_failure(),
            }
            continue;
        }
        // Claim and validate the destination before skipping whitespace or
        // reading the field.
        let index = claimed;
        let store_err = |err| Stop::Store { index, err };
        let limit = if d.suppress {
            None
        } else {
            match args.prepare(&d) {
                Ok(limit) => {
                    claimed += 1;
                    limit
                }
                Err(err) => return store_err(err),
            }
        };
        if d.skips_space() {
            s.skip_space();
        }
        let width = d.width.map_or(usize::MAX, |w| w.get());
        let store = |args: &mut A, v: Value<'_>| {
            if d.suppress {
                Ok(())
            } else {
                args.store(&d, v).map_err(store_err)
            }
        };
        let result = match d.conv {
            Conv::Count => {
                if let Err(stop) = store(args, Value::Count(s.consumed)) {
                    return stop;
                }
                continue;
            }
            Conv::Int { base, .. } => s.int(base, width).map(|v| store(args, v)),
            Conv::Float => s
                .float(width, d.len == LengthMod::L)
                .map(|v| store(args, v)),
            Conv::Chars => {
                let wanted = d.width.map_or(1, |w| w.get());
                if limit.is_some_and(|room| room < wanted) {
                    return store_err(StoreError::Capacity);
                }
                let retained = s.input.recent(0).is_some();
                let n = s.field(wanted, retained, |_| true);
                if n < wanted {
                    Err(if n == 0 {
                        s.empty_item()
                    } else {
                        Fail::Matching
                    })
                } else {
                    Ok(store(args, Value::Bytes(s.field_bytes(n, retained))))
                }
            }
            Conv::Str | Conv::Set(_) => {
                let set = match d.conv {
                    Conv::Set(set) => Some(set),
                    _ => None,
                };
                let accept = |b: u8| match &set {
                    Some(set) => set.contains(b),
                    None => !is_space(b),
                };
                let room = limit.unwrap_or(usize::MAX);
                let retained = s.input.recent(0).is_some();
                let n = s.field(width.min(room), retained, accept);
                // The destination's room, not the width, ended the field if
                // another qualifying byte follows. Peek at it, but leave it
                // and the rest of the field unread.
                let overflow = room < width && n == room && s.peek().is_some_and(accept);
                if n == 0 && !overflow {
                    Err(s.empty_item())
                } else {
                    // On overflow the destination still receives the prefix
                    // that fits, but the conversion does not complete.
                    match store(args, Value::Bytes(s.field_bytes(n, retained))) {
                        Ok(()) if overflow => return store_err(StoreError::Capacity),
                        stored => Ok(stored),
                    }
                }
            }
            Conv::Percent => unreachable!(),
        };
        match result {
            Ok(Ok(())) => {
                *any_input = true;
                if !d.suppress {
                    *assigned += 1;
                }
            }
            Ok(Err(stop)) => return stop,
            Err(Fail::Matching) => return Stop::MatchingFailure,
            Err(Fail::Input) => return s.input_failure(),
        }
    }
    Stop::FormatEnd
}
