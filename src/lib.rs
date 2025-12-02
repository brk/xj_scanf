use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScanError {
    InvalidFormat,
    MatchFailure,
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

pub type ScanResult<T> = Result<T, ScanError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LengthModifier {
    None,
    Hh, // char
    H,  // short
    L,  // long
    Ll, // long long
    J,  // intmax_t
    Z,  // size_t
    T,  // ptrdiff_t
}

#[derive(Debug, Clone)]
pub enum ConversionSpec {
    SignedInt(LengthModifier),
    UnsignedInt(LengthModifier),
    OctalInt(LengthModifier),
    HexInt(LengthModifier),
    AutoInt(LengthModifier), // %i - auto-detect base
    Float(LengthModifier),
    String,
    Char(usize), // count
    CharSet { inverted: bool, chars: String },
    Pointer,
    Position, // %n
    Literal(char),
    Percent,
}

#[derive(Debug)]
pub struct FormatSpec {
    pub suppress: bool,
    pub width: Option<usize>,
    pub conversion: ConversionSpec,
}

#[derive(Debug, PartialEq)]
pub enum ScanValue {
    I32(i32),
    I64(i64),
    U32(u32),
    U64(u64),
    F32(f32),
    F64(f64),
    String(String),
    Char(char),
    Chars(Vec<u8>),
    Position(usize),
}

struct Parser<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Parser {
            input: input.as_bytes(),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<u8> {
        if self.pos < self.input.len() {
            Some(self.input[self.pos])
        } else {
            None
        }
    }

    fn consume(&mut self) -> Option<u8> {
        if self.pos < self.input.len() {
            let ch = self.input[self.pos];
            self.pos += 1;
            Some(ch)
        } else {
            None
        }
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
                width = Some(width_str.parse().unwrap());
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

pub fn sscanf_core(input: &str, format: &str) -> ScanResult<(Vec<ScanValue>, usize)> {
    let specs = parse_format(format)?;
    let mut parser = Parser::new(input);
    let mut values = Vec::new();
    let mut assigned_count = 0;

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
                            assigned_count += 1;
                        }
                    }
                    Err(e) => {
                        if assigned_count == 0 {
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
                            assigned_count += 1;
                        }
                    }
                    Err(e) => {
                        if assigned_count == 0 {
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
                            assigned_count += 1;
                        }
                    }
                    Err(e) => {
                        if assigned_count == 0 {
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
                            assigned_count += 1;
                        }
                    }
                    Err(e) => {
                        if assigned_count == 0 {
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
                            assigned_count += 1;
                        }
                    }
                    Err(e) => {
                        if assigned_count == 0 {
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
                            assigned_count += 1;
                        }
                    }
                    Err(e) => {
                        if assigned_count == 0 {
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
                            assigned_count += 1;
                        }
                    }
                    Err(e) => {
                        if assigned_count == 0 && e == ScanError::Eof {
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
                        assigned_count += 1;
                    }
                }
                Err(e) => {
                    if assigned_count == 0 {
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
                        assigned_count += 1;
                    }
                }
                Err(e) => {
                    if assigned_count == 0 {
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
                        Some(_other_ch) => {
                            // Mismatch
                            parser.pos -= 1; // "un-consume"
                            if assigned_count == 0 {
                                return Err(ScanError::MatchFailure);
                            }
                            break;
                        }
                        None => {
                            // EOF
                            if assigned_count == 0 {
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
                    if assigned_count == 0 {
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

    Ok((values, assigned_count))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_decimal_int() {
        let (values, count) = sscanf_core("42", "%d").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 42),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_negative_int() {
        let (values, count) = sscanf_core("-123", "%d").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, -123),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_multiple_ints() {
        let (values, count) = sscanf_core("1 2 3", "%d %d %d").unwrap();
        assert_eq!(count, 3);
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
        let (values, count) = sscanf_core("4294967295", "%u").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 4294967295),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_octal_int() {
        let (values, count) = sscanf_core("755", "%o").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 0o755),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_hex_int() {
        let (values, count) = sscanf_core("1a2b", "%x").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 0x1a2b),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_hex_with_prefix() {
        let (values, count) = sscanf_core("0xDEAD", "%x").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::U32(x) => assert_eq!(x, 0xDEAD),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_i_decimal() {
        let (values, count) = sscanf_core("123", "%i").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 123),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_i_octal() {
        let (values, count) = sscanf_core("0755", "%i").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 0o755),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_i_hex() {
        let (values, count) = sscanf_core("0x1A", "%i").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 0x1A),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_float_basic() {
        let (values, count) = sscanf_core("3.14", "%f").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::F32(x) => assert!((x - 3.14).abs() < 0.001),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_float_negative() {
        let (values, count) = sscanf_core("-2.5", "%f").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::F32(x) => assert!((x + 2.5).abs() < 0.001),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_float_exponent() {
        let (values, count) = sscanf_core("1.5e2", "%f").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::F32(x) => assert!((x - 150.0).abs() < 0.001),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_string_basic() {
        let (values, count) = sscanf_core("hello", "%s").unwrap();
        assert_eq!(count, 1);
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "hello"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_string_stops_at_whitespace() {
        let (values, count) = sscanf_core("hello world", "%s").unwrap();
        assert_eq!(count, 1);
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "hello"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_string_with_width() {
        let (values, count) = sscanf_core("verylongword", "%5s").unwrap();
        assert_eq!(count, 1);
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "veryl"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_multiple_strings() {
        let (values, count) = sscanf_core("hello world", "%s %s").unwrap();
        assert_eq!(count, 2);
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
        let (values, count) = sscanf_core("A", "%c").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::Char(c) => assert_eq!(c, 'A'),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_char_no_whitespace_skip() {
        let (values, count) = sscanf_core(" A", "%c").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::Char(c) => assert_eq!(c, ' '),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_char_multiple() {
        let (values, count) = sscanf_core("ABCD", "%3c").unwrap();
        assert_eq!(count, 1);
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
        let (values, count) = sscanf_core("abc123", "%[a-z]").unwrap();
        assert_eq!(count, 1);
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "abc"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_charset_inverted() {
        let (values, count) = sscanf_core("abc:def", "%[^:]").unwrap();
        assert_eq!(count, 1);
        match &values[0] {
            ScanValue::String(s) => assert_eq!(s, "abc"),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_suppression_int() {
        let (values, count) = sscanf_core("1 2 3", "%*d %d %*d").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 2),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_n_at_end() {
        let (values, count) = sscanf_core("123", "%d%n").unwrap();
        assert_eq!(count, 1);
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
        let (values, count) = sscanf_core("1,2", "%d,%d").unwrap();
        assert_eq!(count, 2);
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
        let result = sscanf_core("", "%d");
        assert_eq!(result, Err(ScanError::Eof));
    }

    #[test]
    fn test_matching_failure() {
        let result = sscanf_core("abc", "%d");
        assert_eq!(result, Err(ScanError::MatchFailure));
    }

    #[test]
    fn test_partial_match() {
        let (values, count) = sscanf_core("123 abc", "%d %d").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 123),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_percent_literal() {
        let (values, count) = sscanf_core("%42", "%%%d").unwrap();
        assert_eq!(count, 1);
        match values[0] {
            ScanValue::I32(x) => assert_eq!(x, 42),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_eof_in_format() {
        let (values, count) = sscanf_core("0", "%f%c").unwrap();
        assert_eq!(count, 1);
        assert_eq!(values.len(), 1);
        match values[0] {
            ScanValue::F32(f) => assert_eq!(f, 0.0f32),
            _ => panic!("Wrong type"),
        }
    }

    #[test]
    fn test_literal_eof() {
        let result = sscanf_core("", "a");
        assert_eq!(result, Err(ScanError::Eof));
    }

    #[test]
    fn test_bytes_consumed_at_eof() {
        let (values, count) = sscanf_core("aa", "%s%n").unwrap();
        assert_eq!(count, 1);
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
}
