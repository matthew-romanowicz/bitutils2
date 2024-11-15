use std::str::FromStr;

use self::common::ByteSlice;
use self::decimal::{FromDecimal, Decimal};

mod common;
mod decimal;

pub struct Semb<const S: usize, const E: usize, const M: usize, const B: i32> {
    m: u128, // Mantissa
    e: i128, // Biased exponent
    s: u8 // sign
}

impl<const S: usize, const E: usize, const M: usize, const B: i32> Semb<S, E, M, B> {

    // https://doc.rust-lang.org/src/core/num/dec2flt/decimal.rs.html
    const fn min_exponent() -> i32 {
        1 - (B as i32)
    }

    const fn infinite_power() -> i32 {
        (1 << E) - 1
    }

    const fn max_mantissa() -> u128 {
        u128::MAX >> (128 - M)
    }

    const fn signalling_mask() -> u128 {
        1 << (M - 1)
    }

    fn max_decimal_power() -> i32 {
        // Plus one to account for the fact that Decimal is formatted as 0.xxxeyyy
        (((1 << E) - B) as f64 * 2.0_f64.log10()).ceil() as i32 + 1
    }

    fn min_decimal_power() -> i32 {
        (-(B + M as i32) as f64 * 2.0_f64.log10()).floor() as i32
    }

    const fn qnan(negative: bool) -> Self {
        Semb {
            m: 1_u128 << (M as u128 - 1),
            e: Self::infinite_power() as i128,
            s: match negative {true => 1, false => 0}
        }
    }

    const fn snan(negative: bool) -> Self {
        Semb {
            m: 1 as u128,
            e: Self::infinite_power() as i128,
            s: match negative {true => 1, false => 0}
        }
    }

    const fn inf(negative: bool) -> Self {
        Semb {
            m: 0 as u128,
            e: Self::infinite_power() as i128,
            s: match negative {true => 1, false => 0}
        }
    }

    fn max_digits() -> usize {
        // Python: -emin + p2 + math.floor((emin+ 1)*math.log(2, b)-math.log(1-2**(-p2), b))
        let emin = Self::min_exponent() as f64;
        // Note that precision is the length of the mantissa + 1
        let p2 = M as i32 + 1;
        let max_digits = -emin + p2 as f64 + ((emin+ 1.0)*(2.0_f64).log10()-(1.0-2.0_f64.powi(-p2)).log10()).floor();
        return max_digits as usize + 1
    }

    #[inline]
    pub const fn zero_pow2(e: i32) -> Self {
        Self { m: 0, e: e as i128, s: 0}
    }

    /// Returns `true` is `self` is NaN.
    /// # Examples
    ///```rust
    /// use std::str::FromStr;
    /// use bitutils2::semb::SembF128;
    ///
    /// // Positive quiet NaN is NaN
    /// let pos_qnan = SembF128::from_str("nan").unwrap();
    /// assert!(pos_qnan.is_nan());
    ///
    /// // Negative signalling NaN is NaN
    /// let neg_snan = SembF128::from_str("-snan").unwrap();
    /// assert!(neg_snan.is_nan());
    ///
    /// // Infinity is not NaN
    /// let pos_inf = SembF128::from_str("inf").unwrap();
    /// assert!(!pos_inf.is_nan());
    ///
    /// // Normal number is not NaN
    /// let num = SembF128::from_str("3.1415").unwrap();
    /// assert!(!num.is_nan());
    ///```
    pub fn is_nan(&self) -> bool {
        self.e == Self::infinite_power() as i128 && self.m != 0
    }

    /// Returns `true` is `self` is infinite.
    /// # Examples
    ///```rust
    /// use std::str::FromStr;
    /// use bitutils2::semb::SembF128;
    ///
    /// // NaN is not infinite
    /// let pos_qnan = SembF128::from_str("nan").unwrap();
    /// assert!(!pos_qnan.is_infinite());
    ///
    /// // Negative infinity is infinite
    /// let pos_inf = SembF128::from_str("-inf").unwrap();
    /// assert!(pos_inf.is_infinite());
    ///
    /// // Infinity is infinite
    /// let pos_inf = SembF128::from_str("inf").unwrap();
    /// assert!(pos_inf.is_infinite());
    ///
    /// // Normal number is not infinite
    /// let num = SembF128::from_str("3.1415").unwrap();
    /// assert!(!num.is_infinite());
    ///```
    pub fn is_infinite(&self) -> bool {
        self.e == Self::infinite_power() as i128 && self.m == 0
    }

    /// Returns `true` is `self` is not infinite or NaN.
    /// # Examples
    ///```rust
    /// use std::str::FromStr;
    /// use bitutils2::semb::SembF128;
    ///
    /// // NaN is not finite
    /// let pos_qnan = SembF128::from_str("nan").unwrap();
    /// assert!(!pos_qnan.is_finite());
    ///
    /// // Negative infinity is not finite
    /// let pos_inf = SembF128::from_str("-inf").unwrap();
    /// assert!(!pos_inf.is_finite());
    ///
    /// // Infinity is not finite
    /// let pos_inf = SembF128::from_str("inf").unwrap();
    /// assert!(!pos_inf.is_finite());
    ///
    /// // Normal number is finite
    /// let num = SembF128::from_str("3.1415").unwrap();
    /// assert!(num.is_finite());
    ///```
    pub fn is_finite(&self) -> bool {
        self.e != Self::infinite_power() as i128
    }

    /// Returns a tuple of sign, exponent, and mantissa values as integers
    /// that uniquely represent the value of `self`, whether `self` be normal,
    /// subnormal, infinite, signalling NaN, or quiet NaN. In cases where there
    /// are bits that do not impact the value of `self`, those bits are changed
    /// to a canonical representation so that any given value maps to exactly one
    /// canonical form.
    pub fn canonical_form(&self) -> (u8, i128, u128) {
        let s = self.s & 0x01;
        let e = self.e & Self::infinite_power() as i128;
        let m = self.m & Self::max_mantissa();
        if e == Self::infinite_power() as i128 {
            // Infinity
            if m == 0 {
                return (s, e, m)
            // Signalling NaN
            } else if m & Self::signalling_mask() != 0 {
                return (s, e, m & Self::signalling_mask())
            // Quiet NaN
            } else {
                return (s, e, 1)
            }
        } else {
            return (s, e, m)
        }
    }

    // TODO: Is it correct to sub MINIMUM_EXPONENT for -B?
    // https://doc.rust-lang.org/src/core/num/dec2flt/slow.rs.html
    fn parse_long_mantissa<T: std::ops::Shr<usize> + std::ops::Shl<usize> + FromDecimal>(s: &[u8], negative: bool) -> Self {
        const MAX_SHIFT: usize = 60;
        const NUM_POWERS: usize = 19;
        const POWERS: [u8; 19] =
            [0, 3, 6, 9, 13, 16, 19, 23, 26, 29, 33, 36, 39, 43, 46, 49, 53, 56, 59];

        let get_shift = |n| {
            if n < NUM_POWERS { POWERS[n] as usize } else { MAX_SHIFT }
        };

        let fp_zero = Self::zero_pow2(0);
        let fp_inf = Self::zero_pow2(Self::infinite_power());

        let mut d = Decimal::<T>::parse_decimal(Self::max_digits(), s);

        // Short-circuit if the value can only be a literal 0 or infinity.
        // if d.num_digits == 0 || d.decimal_point < -324 {
            if d.num_digits == 0 || d.decimal_point < Self::min_decimal_power() {
            return fp_zero;
        // } else if d.decimal_point >= 310 {
        } else if d.decimal_point >= Self::max_decimal_power() {
            return fp_inf;
        }
        let mut exp2 = 0_i32;
        // Shift right toward (1/2 ... 1].
        while d.decimal_point > 0 {
            let n = d.decimal_point as usize;
            let shift = get_shift(n);
            d.right_shift(shift);
            // println!("1: Right shifted by {}: {}", shift, d);
            if d.decimal_point < -Decimal::<T>::DECIMAL_POINT_RANGE {
                return fp_zero;
            }
            exp2 += shift as i32;
        }
        // Shift left toward (1/2 ... 1].
        while d.decimal_point <= 0 {
            let shift = if d.decimal_point == 0 {
                match d.digits[0] {
                    digit if digit >= 5 => break,
                    0 | 1 => 2,
                    _ => 1,
                }
            } else {
                get_shift((-d.decimal_point) as _)
            };
            d.left_shift(shift);
            // println!("2: Left shifted by {}: {}", shift, d);
            if d.decimal_point > Decimal::<u128>::DECIMAL_POINT_RANGE {
                return fp_inf;
            }
            exp2 -= shift as i32;
        }
        // We are now in the range [1/2 ... 1] but the binary format uses [1 ... 2].
        exp2 -= 1;
        while (-B + 1) > exp2 {
            let mut n = ((-B + 1) - exp2) as usize;
            if n > MAX_SHIFT {
                n = MAX_SHIFT;
            }
            d.right_shift(n);
            // println!("3: Right shifted by {}: {}", n, d);
            exp2 += n as i32;
        }
        if (exp2 - -B) >= Self::infinite_power() {
            return fp_inf;
        }
        // Shift the decimal to the hidden bit, and then round the value
        // to get the high mantissa+1 bits.

        // MAR
        let mut current_shift = M + 1;
        while current_shift > MAX_SHIFT {
            d.left_shift(MAX_SHIFT);
            // println!("4: Left shifted by {}: {}", MAX_SHIFT, d);
            current_shift -= MAX_SHIFT;
        }
        d.left_shift(current_shift);
        // println!("5: Left shifted by {}: {}", current_shift, d);
        // /MAR
        // d.left_shift(M + 1);
        let mut mantissa: T = d.round();
        if mantissa >= (<u8 as Into<T>>::into(1) << (M + 1)) {
            // Rounding up overflowed to the carry bit, need to
            // shift back to the hidden bit.
            d.right_shift(1);
            // println!("6: Right shifted by {}: {}", 1, d);
            exp2 += 1;
            mantissa = d.round();
            if (exp2 - -B) >= Self::infinite_power() {
                return fp_inf;
            }
        }
        let mut power2 = exp2 - -B;
        if mantissa < (<u8 as Into<T>>::into(1) << M).into() {
            power2 -= 1;
        }

        // Zero out all the bits above the explicit mantissa bits.
        mantissa &= (<u8 as Into<T>>::into(1) << M) - 1.into();

        Self {
            m: mantissa.into_u128(),
            e: power2 as i128,
            s: match negative {true => 1, false => 0}
        }
        // BiasedFp { f: mantissa, e: power2 }
    }

    // https://doc.rust-lang.org/src/core/num/dec2flt/parse.rs.html
    /// Try to parse a special, non-finite float.
    fn parse_inf_nan(s: &[u8], negative: bool) -> Option<Self> {
        // Since a valid string has at most the length 8, we can load
        // all relevant characters into a u64 and work from there.
        // This also generates much better code.

        let mut register;
        let len: usize;

        // All valid strings are either of length 8, 4, or 3.
        if s.len() == 8 {
            register = s.read_u64();
            len = 8;
        } else if s.len() == 3 {
            let a = s[0] as u64;
            let b = s[1] as u64;
            let c = s[2] as u64;
            register = (c << 16) | (b << 8) | a;
            len = 3;
        } else if s.len() == 4 {
            let a = s[0] as u64;
            let b = s[1] as u64;
            let c = s[2] as u64;
            let d = s[3] as u64;
            register = (d << 24) | (c << 16) | (b << 8) | a;
            len = 4;
        } else {
            return None;
        }

        // Clear out the bits which turn ASCII uppercase characters into
        // lowercase characters. The resulting string is all uppercase.
        // What happens to other characters is irrelevant.
        register &= 0xDFDFDFDFDFDFDFDF;

        // u64 values corresponding to relevant cases
        const INF_3: u64 = 0x464E49; // "INF"
        const INF_8: u64 = 0x5954494E49464E49; // "INFINITY"
        const NAN: u64 = 0x4E414E; // "NAN"
        const SNAN: u64 = 0x4E414E53; // "SNAN"
        const QNAN: u64 = 0x4E414E51; // "QNAN"

        // Match register value to constant to parse string.
        // Also match on the string length to catch edge cases
        // like "inf\0\0\0\0\0".
        let float = match (register, len) {
            (INF_3, 3) | (INF_8, 8) => Self::inf(negative),
            (NAN, 3) | (QNAN, 4) => Self::qnan(negative),
            (SNAN, 4) => Self::snan(negative),
            _ => return None,
        };

        Some(float)
    }

    fn to_f64(&self) -> f64 {
        let mut bits: u64 = self.m as u64 & 0x000FFFFFFFFFFFFF;
        bits |= (self.e as u64 & 0x7FF) << 52;
        bits |= ((self.s & 0x01 ) as u64) << 63;
        f64::from_bits(bits)
    }

    fn to_f32(&self) -> f32 {
        let mut bits: u32 = self.m as u32 & 0x0007FFFFF;
        bits |= (self.e as u32 & 0xFF) << 23;
        bits |= ((self.s & 0x01 ) as u32) << 31;
        f32::from_bits(bits)
    }
}

impl<const S: usize, const E: usize, const M: usize, const B: i32> PartialEq for Semb<S, E, M, B> {
    fn eq(&self, other: &Semb<S, E, M, B>) -> bool {
        if self.is_nan() || other.is_nan() {
            false
        } else {
            let (s1, e1, m1) = self.canonical_form();
            let (s2, e2, m2) = other.canonical_form();
            if e1 == 0 && e2 == 0 && m1 == 0 && m2 == 0 {
                // 0 == 0 regardless of sign
                true
            } else {
                (s1, e1, m1) == (s2, e2, m2)
            }
        }
    }
}

impl<const S: usize, const E: usize, const M: usize, const B: i32> PartialOrd for Semb<S, E, M, B> {
    fn partial_cmp(&self, other: &Semb<S, E, M, B>) -> Option<std::cmp::Ordering> {

        // If either value is NaN, then the values are non-orderable
        if self.is_nan() || other.is_nan() {
            None

        } else {
            let (s1, e1, m1) = self.canonical_form();
            let (s2, e2, m2) = other.canonical_form();

            // Signs differ
            if s1 != s2 {
                if e1 == 0 && e2 == 0 && m1 == 0 && m2 == 0 {
                    // 0 == 0 regardless of sign
                    Some(std::cmp::Ordering::Equal)
                } else if s1 == 1 {
                    // Self is negative
                    Some(std::cmp::Ordering::Less)
                } else {
                    // Self is positive
                    Some(std::cmp::Ordering::Greater)
                }

            // Exponents differ
            } else if e1 != e2 {
                if s1 == 0 { // Self and other are positive
                    e1.partial_cmp(&e2)
                } else { // Self and other are negative
                    e2.partial_cmp(&e1)
                }
            
            // Signs and exponents are equal, compare mantissas
            } else {
                if s1 == 0 { // Self and other are positive
                    m1.partial_cmp(&m2)
                } else { // Self and other are negative
                    m2.partial_cmp(&m1)
                }
            }

        }
    }
}

#[derive(Clone, Debug)]
enum ParseSembErrorKind {
    Empty,
    UnexpectedEndOfInput,
    InvalidCharacter(usize)
}

#[derive(Clone, Debug)]
pub struct ParseSembError {
    kind: ParseSembErrorKind
}

impl ParseSembError {
    fn new(kind: ParseSembErrorKind) -> ParseSembError {
        ParseSembError {kind}
    }

    fn empty() -> ParseSembError {
        ParseSembError::new(ParseSembErrorKind::Empty)
    }

    fn eoi() -> ParseSembError {
        ParseSembError::new(ParseSembErrorKind::UnexpectedEndOfInput)
    }
}

impl std::fmt::Display for ParseSembError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            ParseSembErrorKind::Empty => write!(f, "Input is empty"),
            ParseSembErrorKind::UnexpectedEndOfInput => write!(f, "Encountered unexpected end of input"),
            ParseSembErrorKind::InvalidCharacter(i) => write!(f, "Invalid character encountered at position {}", i)
        }
    }    
}

impl<const S: usize, const E: usize, const M: usize, const B: i32> FromStr for Semb<S, E, M, B> {
    type Err = ParseSembError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = s.as_bytes();
        let c = if let Some(&c) = s.first() {
            c
        } else {
            return Err(ParseSembError::empty());
        };
        let negative = c == b'-';
        if c == b'-' || c == b'+' {
            s = &s[1..];
        }
        if s.is_empty() {
            return Err(ParseSembError::eoi());
        }

        match Self::parse_inf_nan(s, negative) {
            Some(f) => Ok(f),
            None => Ok(Self::parse_long_mantissa::<u128>(s, negative))
        }
    }
}

// https://en.wikipedia.org/wiki/Bfloat16_floating-point_format
pub type SembBrainF16 = Semb<1, 8, 7, 127>;

// https://en.wikipedia.org/wiki/TensorFloat-32
// TODO: Bias is inferred. Have not found explicit documentation that supports this
pub type SembTensorF32 = Semb<1, 8, 10, 127>;

pub type SembF16 = Semb<1, 5, 10, 15>;
pub type SembF32 = Semb<1, 8, 23, 127>;
pub type SembF64 = Semb<1, 11, 52, 1023>;
pub type SembF128 = Semb<1, 15, 112, 16383>;

#[cfg(test)]
mod semb_tests {
    use std::str::FromStr;
    use super::*;

    #[test]
    fn semb_ord_test() {

        // Negative infinity
        let f1 = SembF32::from_str("-inf").unwrap();

        // Negative normal numbers
        let f2 = SembF32::from_str("-200e5").unwrap();
        let f3 = SembF32::from_str("-100e5").unwrap();
        let f4 = SembF32::from_str("-3.140625").unwrap();
        let f4 = SembF32::from_str("-2.0").unwrap();
        let f5 = SembF32::from_str("-1.0").unwrap();

        // Negative subnormal numbers
        let f6 = SembF32::from_str("-3.0e-30").unwrap();
        let f7 = SembF32::from_str("-1.5e-30").unwrap();
        let f8 = SembF32::from_str("-1.5e-40").unwrap();

        // Zero
        let f9 = SembF32::from_str("0.0").unwrap();

        // Positive subnormal numbers
        let f10 = SembF32::from_str("1.5e-40").unwrap();
        let f11 = SembF32::from_str("1.5e-30").unwrap();
        let f12 = SembF32::from_str("3.0e-30").unwrap();

        // Positive normal numbers
        let f13 = SembF32::from_str("1.0").unwrap();
        let f14 = SembF32::from_str("2.0").unwrap();
        let f15 = SembF32::from_str("3.140625").unwrap();
        let f16 = SembF32::from_str("100e5").unwrap();
        let f17 = SembF32::from_str("200e5").unwrap();

        // Positive infinity
        let f18 = SembF32::from_str("inf").unwrap();

        let nums = vec![
            f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18
        ];

        let pos_qnan = SembF32::from_str("nan").unwrap();
        let neg_qnan = SembF32::from_str("-nan").unwrap();
        let pos_snan = SembF32::from_str("snan").unwrap();
        let neg_snan = SembF32::from_str("-snan").unwrap();

        let nans = vec![
            pos_qnan, neg_qnan, pos_snan, neg_snan
        ];

        for nan1 in &nans {
            for f in &nums {
                assert!(f.partial_cmp(&nan1).is_none());
                assert!(nan1.partial_cmp(&f).is_none());
            }
            for nan2 in &nans {
                assert!(nan1.partial_cmp(&nan2).is_none());
            }
        }

        for (i, f) in nums.iter().enumerate() {
            for (j, g) in nums.iter().enumerate() {
                if i < j {
                    assert!(f != g);
                    assert!(f < g);
                    assert!(f <= g);
                    assert!(!(f == g));
                    assert!(!(f > g));
                    assert!(!(f >= g));
                } else if i == j {
                    assert!(f == g);
                    assert!(f >= g);
                    assert!(f <= g);
                    assert!(!(f != g));
                    assert!(!(f < g));
                    assert!(!(f > g));
                } else {
                    assert!(f != g);
                    assert!(f > g);
                    assert!(f >= g);
                    assert!(!(f == g));
                    assert!(!(f < g));
                    assert!(!(f <= g));
                }
            }
        }
    }

    #[test]
    fn semb_eq_test() {
        let f1 = SembF32::from_str("3.140625").unwrap();
        let f2 = SembF32::from_str("3.140625").unwrap();
        assert!(f1 == f2);

        let f1 = SembF32::from_str("-3.140625").unwrap();
        let f2 = SembF32::from_str("-3.140625").unwrap();
        assert!(f1 == f2);

        let f1 = SembF32::from_str("-3.140625").unwrap();
        let f2 = SembF32::from_str("3.140625").unwrap();
        assert!(f1 != f2);

        let f1 = SembF32::from_str("3.140626").unwrap();
        let f2 = SembF32::from_str("3.140625").unwrap();
        assert!(f1 != f2);

        let f1 = SembF32::from_str("1.0").unwrap();
        let f2 = SembF32::from_str("2.0").unwrap();
        assert!(f1 != f2);

        let f1 = SembF32::from_str("infinity").unwrap();
        let f2 = SembF32::from_str("inf").unwrap();
        assert!(f1 == f2);

        let f1 = SembF32::from_str("-infinity").unwrap();
        let f2 = SembF32::from_str("-inf").unwrap();
        assert!(f1 == f2);

        let f1 = SembF32::from_str("infinity").unwrap();
        let f2 = SembF32::from_str("-inf").unwrap();
        assert!(f1 != f2);

        let f1 = SembF32::from_str("nan").unwrap();
        let f2 = SembF32::from_str("inf").unwrap();
        assert!(f1 != f2);

        let f1 = SembF32::from_str("nan").unwrap();
        let f2 = SembF32::from_str("nan").unwrap();
        assert!(f1 != f2);

        let f1 = SembF32::from_str("-nan").unwrap();
        let f2 = SembF32::from_str("-nan").unwrap();
        assert!(f1 != f2);

        let f1 = SembF32::from_str("-0.0").unwrap();
        let f2 = SembF32::from_str("0e10").unwrap();
        assert!(f1 == f2);
    }

    #[test]
    fn semb_bf16_test() {
        // Pi
        let f = SembBrainF16::from_str("3.140625").unwrap();
        assert_eq!(f.m, 0b1001001);
        assert_eq!(f.e, 0b10000000);

        // 1/3
        let f = SembBrainF16::from_str("0.33333333").unwrap();
        assert_eq!(f.m, 0b0101011);
        assert_eq!(f.e, 0b01111101);
        
    }

    #[test]
    fn semb_f128_test() {
        // f = (m / (2^112) + 1) * 2^(e - 16383)

        // panic!("{}", SembF128::min_decimal_power());

        // Largest number less than 1
        let f = SembF128::from_str("0.9999999999999999999999999999999999037").unwrap();
        assert_eq!(f.m, 0xffffffffffffffffffffffffffff);
        assert_eq!(f.e, 0x3ffe);

        // Smallest number larger than 1
        let f = SembF128::from_str("1.0000000000000000000000000000000001926").unwrap();
        assert_eq!(f.m, 0x0000000000000000000000000001);
        assert_eq!(f.e, 0x3fff);

        // Smallest number larger than 1
        let f = SembF128::from_str("100000000000000000.00000000000000001926e-17").unwrap();
        assert_eq!(f.m, 0x0000000000000000000000000001);
        assert_eq!(f.e, 0x3fff);

        // Largest normal number
        let f = SembF128::from_str("1.1897314953572317650857593266280070162e4932").unwrap();
        assert_eq!(f.m, 0xffffffffffffffffffffffffffff);
        assert_eq!(f.e, 0x7ffe);

        // Somewhat smallish normal number
        let f = SembF128::from_str("3.3621031431120935062626778173217526026e-1000").unwrap();
        assert_eq!(f.m, 3982282193971599414176888659273906);
        assert_eq!(f.e, 13062);

        // Very smallish normal number
        let f = SembF128::from_str("3.3621031431120935062626778173217526026e-4931").unwrap();
        assert_eq!(f.m, 1298074214633706907132624082305024);
        assert_eq!(f.e, 4);

        // Second smallest normal number
        let f = SembF128::from_str("3.3621031431120935062626778173217532501e-4932").unwrap();
        assert_eq!(f.m, 0x0000000000000000000000000001);
        assert_eq!(f.e, 0x0001);

        // Smallest normal number
        let f = SembF128::from_str("3.3621031431120935062626778173217526026e-4932").unwrap();
        assert_eq!(f.m, 0x0000000000000000000000000000);
        assert_eq!(f.e, 0x0001);

        // Halfway between the smallest and second smallest normal number (round down)
        let s = "3.362103143112093506262677817321752926356835316747726786330775141191070324369195\
            868777143190859275682714478912874792024110664675304224690934654568037596615558527\
            720710612100920474398091699640084452218724266606548321708436395305484703786427374\
            809489419091356696204323483265025882415538916845516454253413952077170215480026586\
            346620716479045657017198906456701776021492537839651171762857011876463887001606498\
            816316980482508771459313457671744756205918284923683484130792963720918539433437742\
            364712271994448368165901582521947939760152739330283800384124799074590857330436018\
            454938739011760238843517887132205176939981497944085853405680126274114241477783152\
            618062002091230049784928064269872506839546487556465501607594144031244669616619036\
            349368261108638067419688952942109562501282335771877983613919500375595843624134307\
            697159017316349372630872594708666916290999444646073811198478941774053787401188064\
            609282753674880887387101371168857728832500584400070076384803608662529965000587827\
            575199204888000709134535890916983274104968947036691511095568487992484398307445203\
            185237708899338193072335964290132943120071849556781855039427139191237321375410066\
            859847278725494529869109913914736038298743491103216888506755416358577912094664305\
            080081260781227592514748088678412864677866664010905196569384201693144040668167264\
            091819709351015668523457271345089418506952234954755771713779010825804561455393642\
            150511627020870635494634592754519264185011935479626298514891234004957230510112529\
            878044766045825180668146333580916726113251953127142886427203896310385625679004858\
            552417203471394316757221179955423307922856625964190120946198516434366868212672495\
            895475275844299430782039747741673867370164074405135237670095042536008727867460738\
            551407243123543005101291693106921117196291529057535364631332349035303382269044963\
            210468775461029512947242913965279938995667948426276641020998595177402430404314326\
            176994907667057468455622343598553781281183952627217915445984657879858928039681802\
            660006997487755048154084449691268122176340603713114338811111455235581742205989607\
            515456818859492935446673787055104983806828752e-4932";

        let f = SembF128::from_str(s).unwrap();
        assert_eq!(f.m, 0x0000000000000000000000000000);
        assert_eq!(f.e, 0x0001);

        // Halfway between the smallest and second smallest normal number (round up)
        let s = "3.362103143112093506262677817321752926356835316747726786330775141191070324369195\
            868777143190859275682714478912874792024110664675304224690934654568037596615558527\
            720710612100920474398091699640084452218724266606548321708436395305484703786427374\
            809489419091356696204323483265025882415538916845516454253413952077170215480026586\
            346620716479045657017198906456701776021492537839651171762857011876463887001606498\
            816316980482508771459313457671744756205918284923683484130792963720918539433437742\
            364712271994448368165901582521947939760152739330283800384124799074590857330436018\
            454938739011760238843517887132205176939981497944085853405680126274114241477783152\
            618062002091230049784928064269872506839546487556465501607594144031244669616619036\
            349368261108638067419688952942109562501282335771877983613919500375595843624134307\
            697159017316349372630872594708666916290999444646073811198478941774053787401188064\
            609282753674880887387101371168857728832500584400070076384803608662529965000587827\
            575199204888000709134535890916983274104968947036691511095568487992484398307445203\
            185237708899338193072335964290132943120071849556781855039427139191237321375410066\
            859847278725494529869109913914736038298743491103216888506755416358577912094664305\
            080081260781227592514748088678412864677866664010905196569384201693144040668167264\
            091819709351015668523457271345089418506952234954755771713779010825804561455393642\
            150511627020870635494634592754519264185011935479626298514891234004957230510112529\
            878044766045825180668146333580916726113251953127142886427203896310385625679004858\
            552417203471394316757221179955423307922856625964190120946198516434366868212672495\
            895475275844299430782039747741673867370164074405135237670095042536008727867460738\
            551407243123543005101291693106921117196291529057535364631332349035303382269044963\
            210468775461029512947242913965279938995667948426276641020998595177402430404314326\
            176994907667057468455622343598553781281183952627217915445984657879858928039681802\
            660006997487755048154084449691268122176340603713114338811111455235581742205989607\
            515456818859492935446673787055104983806828753e-4932";

        let f = SembF128::from_str(s).unwrap();
        assert_eq!(f.m, 0x0000000000000000000000000001);
        assert_eq!(f.e, 0x0001);

        // Middlish subnormal number
        let f = SembF128::from_str("6.4751751194380251109244389582276465525e-4940").unwrap();
        assert_eq!(f.m, 100000000000000000000000000);
        assert_eq!(f.e, 0x0000);

        // Smallest subnormal number
        let f = SembF128::from_str("6.4751751194380251109244389582276465525e-4966").unwrap();
        assert_eq!(f.m, 0x0000000000000000000000000001);
        assert_eq!(f.e, 0x0000);

        // Largest subnormal number
        let f = SembF128::from_str("3.3621031431120935062626778173217519551e-4932").unwrap();
        assert_eq!(f.m, 0xffffffffffffffffffffffffffff);
        assert_eq!(f.e, 0x0000);

        // Pi
        let f = SembF128::from_str("3.1415926535897932384626433832795028841").unwrap();
        assert_eq!(f.m, 0x921fb54442d18469898cc51701b8);
        assert_eq!(f.e, 0x4000);
        // panic!("m={}, e={}", f.m, f.e);
    }

    #[test]
    fn semb_f16_test() {
        // Smallest subnormal number
        let f = SembF16::from_str("0.000000059604645").unwrap();
        assert_eq!(f.m, 0b0000000001);
        assert_eq!(f.e, 0b00000);

        // Largest subnormal number
        let f = SembF16::from_str("0.000060975552").unwrap();
        assert_eq!(f.m, 0b1111111111);
        assert_eq!(f.e, 0b00000);

        // Smallest normal number
        let f = SembF16::from_str("0.00006103515625").unwrap();
        assert_eq!(f.m, 0b0000000000);
        assert_eq!(f.e, 0b00001);

        // 1/3
        let f = SembF16::from_str("0.33333333").unwrap();
        assert_eq!(f.m, 0b0101010101);
        assert_eq!(f.e, 0b01101);

        // Largest number less than 1
        let f = SembF16::from_str("0.99951172").unwrap();
        assert_eq!(f.m, 0b1111111111);
        assert_eq!(f.e, 0b01110);

        // 1
        let f = SembF16::from_str("1").unwrap();
        assert_eq!(f.m, 0b0000000000);
        assert_eq!(f.e, 0b01111);

        // Smallest number larger than 1
        let f = SembF16::from_str("1.00097656").unwrap();
        assert_eq!(f.m, 0b0000000001);
        assert_eq!(f.e, 0b01111);

        // Largest normal number
        let f = SembF16::from_str("65504").unwrap();
        assert_eq!(f.m, 0b1111111111);
        assert_eq!(f.e, 0b11110);

        // Round to infinity
        // let f = SembF16::from_str("65510").unwrap();
        // assert_eq!(f.m, 0b0);
        // assert_eq!(f.e, 0b11111);
    }

    #[test]
    fn semb_f64_test() {
        // Float 64
        assert_eq!(SembF64::max_digits(), 768);
        assert_eq!(SembF64::max_decimal_power(), 310);
        assert_eq!(SembF64::min_decimal_power(), -324);

        let test_strings = vec![
            "nan",
            "-nan",
            "inf",
            "-inf",
            "infinity",
            "-infinity",
            "0",
            ".12345e-23",
            ".12345",
            "1.2345",
            "123.45",
            "123.45e+15",
            "12345",
            // https://github.com/rust-lang/rust/blob/master/src/etc/test-float-parse/src/validate/tests.rs
            "1.00000005960464477539062499999",
            "1.000000059604644775390625",
            "1.00000005960464477539062500001",
            "1.00000017881393432617187499999",
            "1.000000178813934326171875",
            "1.00000017881393432617187500001",
            // Minimum positive subnormal value
            "4.94065645841246544176568792868221372365059802614324764425585682500675507270208751865299836361635\
            99237979656469544571773092665671035593979639877479601078187812630071319031140452784581716784898210\
            36887186360569987307230500063874091535649843873124733972731696151400317153853980741262385655911710\
            26658556686768187039560310624931945271591492455329305456544401127480129709999541931989409080416563\
            32452475714786901472678015935523861155013480352649347201937902681071074917033322268447533357208324\
            31936092382893458368060106011506169809753078342277318329247904982524730776375927247874656084778203\
            73446969953364701797267771758512566055119913150489110145103786273816725095583738973359899366480994\
            1164205702637090279242767544565229087538682506419718265533447265625e-324",
            // Max subnormal
            "2.2250738585072009e-308",
            // Min normal
            "2.2250738585072014e-308",
            // Max double
            "1.7976931348623157e308",
            // Smallest number larger than 1 (1 + 2^-52)
            "1.0000000000000002220446049250313080847263336181640625",
            // 1 + 2^-51
            "1.000000000000000444089209850062616169452667236328125",
            // Larger than max double (round to infinity)
            "1.7976931348623167e308",
            "1.798e308",
            "1.7976931348623157e310",

        ];

        for s in test_strings {
            let semb = SembF64::from_str(s).unwrap();
            let f = f64::from_str(s).unwrap();
            assert_eq!(semb.to_f64().to_bits(), f.to_bits());
        }

        let test_pairs = vec![
            ("100000005960464477539062499999", 0),
            ("1000000059604644775390625", 0),
            ("100000005960464477539062500001", 0),
            ("100000017881393432617187499999", 0),
            ("1000000178813934326171875", 0),
            ("100000017881393432617187500001", 0),
            // Max subnormal
            ("22250738585072009", -308),
            // Min normal
            ("22250738585072014", -308),
            // Max double
            ("17976931348623157", 308),
            // Smallest number larger than 1 (1 + 2^-52)
            ("10000000000000002220446049250313080847263336181640625", 0_isize),
            ("10000000000000002220446049250313080847263336181640625", 0_isize)
        ];

        for (m, e) in test_pairs {
            let f = SembF64::from_str(&format!("0.{}e{}", m, e + 1)).unwrap();
            for i in 0..100 {
                let s = format!("0.{}{}e{}", "0".repeat(i), m, e + i as isize + 1);
                // println!("{}", s);
                let f2 = SembF64::from_str(&s).unwrap();
                let f3 = f64::from_str(&s).unwrap(); 
                assert!(f2.to_f64() == f3);
                assert!(f.to_f64() == f2.to_f64());
            }
            for i in 0..m.len() {
                let s = format!("{}.{}e{}", &m[..i], &m[i..], e - i as isize + 1);
                // println!("{}", s);
                let f2 = SembF64::from_str(&s).unwrap();
                let f3 = f64::from_str(&s).unwrap(); 
                assert!(f2.to_f64() == f3);
                assert!(f.to_f64() == f2.to_f64());
            }
            for i in 0..100 {
                let s = format!("{}{}e{}", m, "0".repeat(i), e - i as isize - m.len() as isize + 1);
                // println!("{}", s);
                let f2 = SembF64::from_str(&s).unwrap();
                let f3 = f64::from_str(&s).unwrap(); 
                assert!(f2.to_f64() == f3);
                assert!(f.to_f64() == f2.to_f64());
            }
        }

        let fp = SembF64::from_str("nan").unwrap();
        let fp2 = f64::from_str("nan").unwrap();
        assert_eq!(fp.to_f64().to_bits(), fp2.to_bits());

        let fp = SembF64::from_str("-qnan").unwrap();
        let fp2 = f64::from_str("-nan").unwrap();
        assert_eq!(fp.to_f64().to_bits(), fp2.to_bits());
        // panic!();
    }

    #[test]
    fn semb_f32_test() {

        assert_eq!(SembF32::max_decimal_power(), 40);
        assert_eq!(SembF32::min_decimal_power(), -46); // TODO: Should this be -44?

        let test_strings = vec![
            "nan",
            "-nan",
            "inf",
            "-inf",
            "infinity",
            "-infinity",
            "0",
            ".12345e-23",
            ".12345",
            "1.2345",
            "123.45",
            "123.45e+15",
            "12345",
            // https://github.com/rust-lang/rust/blob/master/src/etc/test-float-parse/src/validate/tests.rs
            "1.00000005960464477539062499999",
            "1.000000059604644775390625",
            "1.00000005960464477539062500001",
            "1.00000017881393432617187499999",
            "1.000000178813934326171875",
            "1.00000017881393432617187500001"
        ];

        for s in test_strings {
            let semb = SembF32::from_str(s).unwrap();
            let f = f32::from_str(s).unwrap();
            assert_eq!(semb.to_f32().to_bits(), f.to_bits());
        }

        let fp = SembF32::from_str("qnan").unwrap();
        let fp2 = f32::from_str("nan").unwrap();
        assert_eq!(fp.to_f32().to_bits(), fp2.to_bits());
    }
}