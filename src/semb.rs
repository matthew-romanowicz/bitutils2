use std::str::FromStr;

trait FromDecimal : Clone + Copy + std::convert::From<u8> + std::ops::Mul<Self, Output = Self> + std::ops::BitAnd<Self, Output = Self> + std::ops::MulAssign + std::ops::AddAssign
        + std::ops::Shr<usize, Output = Self> + std::ops::Shl<usize, Output = Self> + std::ops::Sub<Self, Output = Self> + std::ops::Div<Self, Output = Self> 
        + std::cmp::PartialOrd<Self> + std::ops::BitAndAssign {
    // The max number of decimal digits that can be exactly represented
    const MAX_DIGITS: usize;

    // The max value that can be exactly represented
    const MAX_VALUE: Self;

    fn into_u8(&self) -> u8;

    fn is_zero(&self) -> bool;

    fn gt_zero(&self) -> bool;

    fn into_u128(&self) -> u128;

}

impl FromDecimal for u64 {
    const MAX_DIGITS: usize = Self::MAX.ilog10() as usize;
    const MAX_VALUE: Self = Self::MAX;

    fn into_u8(&self) -> u8 {
        *self as u8
    }

    fn is_zero(&self) -> bool {
        *self == 0
    }

    fn gt_zero(&self) -> bool {
        *self > 0
    }

    fn into_u128(&self) -> u128 {
        *self as u128
    }
}

impl FromDecimal for u128 {
    const MAX_DIGITS: usize = Self::MAX.ilog10() as usize;
    const MAX_VALUE: Self = Self::MAX;

    fn into_u8(&self) -> u8 {
        *self as u8
    }

    fn is_zero(&self) -> bool {
        *self == 0
    }

    fn gt_zero(&self) -> bool {
        *self > 0
    }

    fn into_u128(&self) -> u128 {
        *self
    }
}

// https://nigeltao.github.io/blog/2020/parse-number-f64-simple.html

pub struct Decimal<T> {
    digits: Vec<u8>,
    decimal_point: i32,
    max_digits: usize,
    num_digits: usize,
    truncated: bool,
    phantom: std::marker::PhantomData<T>
}

impl<T> std::fmt::Display for Decimal<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let bytes: Vec<u8> = self.digits.iter().take(self.num_digits).map(|b| b + 0x30).collect();
        if self.truncated {
            write!(f, "0.{}...e{}", std::str::from_utf8(&bytes).unwrap(), self.decimal_point)
        } else {
            write!(f, "0.{}e{}", std::str::from_utf8(&bytes).unwrap(), self.decimal_point)
        }
        
    }
}

impl<T: FromDecimal> Decimal<T> {
    /// The max digits that can be exactly represented in T.
    // pub const MAX_DIGITS_WITHOUT_OVERFLOW: usize = 19;
    pub const MAX_DIGITS_WITHOUT_OVERFLOW: usize = T::MAX_DIGITS;
    pub const DECIMAL_POINT_RANGE: i32 = 2047;

    pub fn new(max_digits: usize) -> Decimal<T> {
        Decimal::<T> {
            digits: vec![0; max_digits],
            decimal_point: 0,
            max_digits,
            num_digits: 0,
            truncated: false,
            phantom: std::marker::PhantomData
        }
    }

    /// Append a digit to the buffer.
    pub fn try_add_digit(&mut self, digit: u8) {
        if self.num_digits < self.max_digits {
            // self.digits.push(digit);
            self.digits[self.num_digits] = digit;
        }
        self.num_digits += 1;
    }

    /// Trim trailing zeros from the buffer.
    pub fn trim(&mut self) {
        // All of the following calls to `Decimal::trim` can't panic because:
        //
        //  1. `parse_decimal` sets `num_digits` to a max of `Decimal::MAX_DIGITS`.
        //  2. `right_shift` sets `num_digits` to `write_index`, which is bounded by `num_digits`.
        //  3. `left_shift` `num_digits` to a max of `Decimal::MAX_DIGITS`.
        //
        // Trim is only called in `right_shift` and `left_shift`.
        debug_assert!(self.num_digits <= self.max_digits);
        while self.num_digits != 0 && self.digits[self.num_digits - 1] == 0 {
            self.num_digits -= 1;
        }
    }

    pub fn round(&self) -> T {
        if self.num_digits == 0 || self.decimal_point < 0 {
            return 0.into();
        } else if self.decimal_point > Self::MAX_DIGITS_WITHOUT_OVERFLOW as i32 - 1 {
            return T::MAX_VALUE;
        }
        let dp = self.decimal_point as usize;
        let mut n: T = 0.into();
        for i in 0..dp {
            n *= 10.into();
            if i < self.num_digits {
                n += self.digits[i].into();
            }
        }
        let mut round_up = false;
        if dp < self.num_digits {
            round_up = self.digits[dp] >= 5;
            if self.digits[dp] == 5 && dp + 1 == self.num_digits {
                round_up = self.truncated || ((dp != 0) && (1 & self.digits[dp - 1] != 0))
            }
        }
        if round_up {
            n += 1.into();
        }
        n
    }

    /// Computes decimal * 2^shift.
    pub fn left_shift(&mut self, shift: usize) {
        println!("Shift: {}", shift);
        if self.num_digits == 0 {
            return;
        }
        let num_new_digits = number_of_digits_decimal_left_shift::<T>(self, shift);
        let mut read_index = self.num_digits;
        let mut write_index = self.num_digits + num_new_digits;
        let mut n: T = 0.into();
        while read_index != 0 {
            read_index -= 1;
            write_index -= 1;
            n += (<u8 as Into<T>>::into(self.digits[read_index])) << shift;
            let quotient: T = n / 10.into();
            let remainder: T = n - (quotient * 10.into());
            if write_index < self.max_digits {
                self.digits[write_index] = remainder.into_u8();
            } else if remainder.gt_zero() {
                self.truncated = true;
            }
            n = quotient;
        }

        while n.gt_zero() {
            write_index -= 1;
            let quotient: T = n / 10.into();
            let remainder: T = n - (quotient * 10.into());
            if write_index < self.max_digits {
                self.digits[write_index] = remainder.into_u8();
            } else if remainder.gt_zero() {
                self.truncated = true;
            }
            n = quotient;
        }
        self.num_digits += num_new_digits;
        if self.num_digits > self.max_digits {
            self.num_digits = self.max_digits;
        }
        self.decimal_point += num_new_digits as i32;
        self.trim();
    }

    /// Computes decimal * 2^-shift.
    pub fn right_shift(&mut self, shift: usize) {
        let mut read_index = 0;
        let mut write_index = 0;
        let mut n: T = 0.into();
        while (n >> shift).is_zero() {
            if read_index < self.num_digits {
                n *= 10.into();
                n += self.digits[read_index].into();
                read_index += 1;
            } else if n.is_zero() {
                return;
            } else {
                while (n >> shift).is_zero() {
                    n *= 10.into();
                    read_index += 1;
                }
                break;
            }
        }
        self.decimal_point -= read_index as i32 - 1;
        if self.decimal_point < -Self::DECIMAL_POINT_RANGE {
            // `self = Self::Default()`, but without the overhead of clearing `digits`.
            self.num_digits = 0;
            self.decimal_point = 0;
            self.truncated = false;
            return;
        }
        let mask = (<u8 as Into<T>>::into(1) << shift) - 1.into();
        while read_index < self.num_digits {
            let new_digit: u8 = (n >> shift).into_u8();
            n = ((n & mask) * 10.into());
            n += self.digits[read_index].into();
            read_index += 1;
            self.digits[write_index] = new_digit;
            write_index += 1;
        }
        while n.gt_zero() {
            let new_digit: u8 = (n >> shift).into_u8();
            n = <u8 as Into<T>>::into(10) * (n & mask);
            if write_index < self.max_digits {
                self.digits[write_index] = new_digit;
                write_index += 1;
            } else if new_digit > 0 {
                self.truncated = true;
            }
        }
        self.num_digits = write_index;
        self.trim();
    }

    /// Parse a big integer representation of the float as a decimal.
    pub fn parse_decimal(max_digits: usize, mut s: &[u8]) -> Self {
        let mut d = Self::new(max_digits);
        let start = s;

        while let Some((&b'0', s_next)) = s.split_first() {
            s = s_next;
        }

        s = s.parse_digits(|digit| d.try_add_digit(digit));

        if let Some((b'.', s_next)) = s.split_first() {
            s = s_next;
            let first = s;
            // Skip leading zeros.
            if d.num_digits == 0 {
                while let Some((&b'0', s_next)) = s.split_first() {
                    s = s_next;
                }
            }
            while s.len() >= 8 && d.num_digits + 8 < max_digits {
                let v = s.read_u64();
                if !is_8digits(v) {
                    break;
                }
                d.digits[d.num_digits..].write_u64(v - 0x3030_3030_3030_3030);
                d.num_digits += 8;
                s = &s[8..];
            }
            s = s.parse_digits(|digit| d.try_add_digit(digit));
            d.decimal_point = s.len() as i32 - first.len() as i32;
        }
        if d.num_digits != 0 {
            // Ignore the trailing zeros if there are any
            let mut n_trailing_zeros = 0;
            for &c in start[..(start.len() - s.len())].iter().rev() {
                if c == b'0' {
                    n_trailing_zeros += 1;
                } else if c != b'.' {
                    break;
                }
            }
            d.decimal_point += n_trailing_zeros as i32;
            d.num_digits -= n_trailing_zeros;
            d.decimal_point += d.num_digits as i32;
            if d.num_digits > max_digits {
                d.truncated = true;
                d.num_digits = max_digits;
            }
        }
        if let Some((&ch, s_next)) = s.split_first() {
            if ch == b'e' || ch == b'E' {
                s = s_next;
                let mut neg_exp = false;
                if let Some((&ch, s_next)) = s.split_first() {
                    neg_exp = ch == b'-';
                    if ch == b'-' || ch == b'+' {
                        s = s_next;
                    }
                }
                let mut exp_num = 0_i32;

                s.parse_digits(|digit| {
                    if exp_num < 0x10000 {
                        exp_num = 10 * exp_num + digit as i32;
                    }
                });

                

                d.decimal_point += if neg_exp { -exp_num } else { exp_num };
            }
        }
        for i in d.num_digits..std::cmp::min(max_digits, Self::MAX_DIGITS_WITHOUT_OVERFLOW) {
            d.digits[i] = 0;
            
        }

        // println!("Parsed decimal: {}", d);
        d
    }
}



fn number_of_digits_decimal_left_shift<T: std::ops::Shr<usize> + FromDecimal>(d: &Decimal<T>, mut shift: usize) -> usize {
    #[rustfmt::skip]
    // First 5 bits of TABLE[n] indicates the maximum number of decimal digits added by a shift of n
    // The last 11 bits of TABLE[n] and TABLE[n+1] indicate the start and end indices of the decimal 
    // digits of the nth power of 5 in TABLE_POW5
    const TABLE: [u16; 65] = [
        0x0000, 0x0800, 0x0801, 0x0803, 0x1006, 0x1009, 0x100D, 0x1812, 0x1817, 0x181D, 0x2024,
        0x202B, 0x2033, 0x203C, 0x2846, 0x2850, 0x285B, 0x3067, 0x3073, 0x3080, 0x388E, 0x389C,
        0x38AB, 0x38BB, 0x40CC, 0x40DD, 0x40EF, 0x4902, 0x4915, 0x4929, 0x513E, 0x5153, 0x5169,
        0x5180, 0x5998, 0x59B0, 0x59C9, 0x61E3, 0x61FD, 0x6218, 0x6A34, 0x6A50, 0x6A6D, 0x6A8B,
        0x72AA, 0x72C9, 0x72E9, 0x7B0A, 0x7B2B, 0x7B4D, 0x8370, 0x8393, 0x83B7, 0x83DC, 0x8C02,
        0x8C28, 0x8C4F, 0x9477, 0x949F, 0x94C8, 0x9CF2, 0x051C, 0x051C, 0x051C, 0x051C,
    ];
    #[rustfmt::skip]
    const TABLE_POW5: [u8; 0x051C] = [
        5, 2, 5, 1, 2, 5, 6, 2, 5, 3, 1, 2, 5, 1, 5, 6, 2, 5, 7, 8, 1, 2, 5, 3, 9, 0, 6, 2, 5, 1,
        9, 5, 3, 1, 2, 5, 9, 7, 6, 5, 6, 2, 5, 4, 8, 8, 2, 8, 1, 2, 5, 2, 4, 4, 1, 4, 0, 6, 2, 5,
        1, 2, 2, 0, 7, 0, 3, 1, 2, 5, 6, 1, 0, 3, 5, 1, 5, 6, 2, 5, 3, 0, 5, 1, 7, 5, 7, 8, 1, 2,
        5, 1, 5, 2, 5, 8, 7, 8, 9, 0, 6, 2, 5, 7, 6, 2, 9, 3, 9, 4, 5, 3, 1, 2, 5, 3, 8, 1, 4, 6,
        9, 7, 2, 6, 5, 6, 2, 5, 1, 9, 0, 7, 3, 4, 8, 6, 3, 2, 8, 1, 2, 5, 9, 5, 3, 6, 7, 4, 3, 1,
        6, 4, 0, 6, 2, 5, 4, 7, 6, 8, 3, 7, 1, 5, 8, 2, 0, 3, 1, 2, 5, 2, 3, 8, 4, 1, 8, 5, 7, 9,
        1, 0, 1, 5, 6, 2, 5, 1, 1, 9, 2, 0, 9, 2, 8, 9, 5, 5, 0, 7, 8, 1, 2, 5, 5, 9, 6, 0, 4, 6,
        4, 4, 7, 7, 5, 3, 9, 0, 6, 2, 5, 2, 9, 8, 0, 2, 3, 2, 2, 3, 8, 7, 6, 9, 5, 3, 1, 2, 5, 1,
        4, 9, 0, 1, 1, 6, 1, 1, 9, 3, 8, 4, 7, 6, 5, 6, 2, 5, 7, 4, 5, 0, 5, 8, 0, 5, 9, 6, 9, 2,
        3, 8, 2, 8, 1, 2, 5, 3, 7, 2, 5, 2, 9, 0, 2, 9, 8, 4, 6, 1, 9, 1, 4, 0, 6, 2, 5, 1, 8, 6,
        2, 6, 4, 5, 1, 4, 9, 2, 3, 0, 9, 5, 7, 0, 3, 1, 2, 5, 9, 3, 1, 3, 2, 2, 5, 7, 4, 6, 1, 5,
        4, 7, 8, 5, 1, 5, 6, 2, 5, 4, 6, 5, 6, 6, 1, 2, 8, 7, 3, 0, 7, 7, 3, 9, 2, 5, 7, 8, 1, 2,
        5, 2, 3, 2, 8, 3, 0, 6, 4, 3, 6, 5, 3, 8, 6, 9, 6, 2, 8, 9, 0, 6, 2, 5, 1, 1, 6, 4, 1, 5,
        3, 2, 1, 8, 2, 6, 9, 3, 4, 8, 1, 4, 4, 5, 3, 1, 2, 5, 5, 8, 2, 0, 7, 6, 6, 0, 9, 1, 3, 4,
        6, 7, 4, 0, 7, 2, 2, 6, 5, 6, 2, 5, 2, 9, 1, 0, 3, 8, 3, 0, 4, 5, 6, 7, 3, 3, 7, 0, 3, 6,
        1, 3, 2, 8, 1, 2, 5, 1, 4, 5, 5, 1, 9, 1, 5, 2, 2, 8, 3, 6, 6, 8, 5, 1, 8, 0, 6, 6, 4, 0,
        6, 2, 5, 7, 2, 7, 5, 9, 5, 7, 6, 1, 4, 1, 8, 3, 4, 2, 5, 9, 0, 3, 3, 2, 0, 3, 1, 2, 5, 3,
        6, 3, 7, 9, 7, 8, 8, 0, 7, 0, 9, 1, 7, 1, 2, 9, 5, 1, 6, 6, 0, 1, 5, 6, 2, 5, 1, 8, 1, 8,
        9, 8, 9, 4, 0, 3, 5, 4, 5, 8, 5, 6, 4, 7, 5, 8, 3, 0, 0, 7, 8, 1, 2, 5, 9, 0, 9, 4, 9, 4,
        7, 0, 1, 7, 7, 2, 9, 2, 8, 2, 3, 7, 9, 1, 5, 0, 3, 9, 0, 6, 2, 5, 4, 5, 4, 7, 4, 7, 3, 5,
        0, 8, 8, 6, 4, 6, 4, 1, 1, 8, 9, 5, 7, 5, 1, 9, 5, 3, 1, 2, 5, 2, 2, 7, 3, 7, 3, 6, 7, 5,
        4, 4, 3, 2, 3, 2, 0, 5, 9, 4, 7, 8, 7, 5, 9, 7, 6, 5, 6, 2, 5, 1, 1, 3, 6, 8, 6, 8, 3, 7,
        7, 2, 1, 6, 1, 6, 0, 2, 9, 7, 3, 9, 3, 7, 9, 8, 8, 2, 8, 1, 2, 5, 5, 6, 8, 4, 3, 4, 1, 8,
        8, 6, 0, 8, 0, 8, 0, 1, 4, 8, 6, 9, 6, 8, 9, 9, 4, 1, 4, 0, 6, 2, 5, 2, 8, 4, 2, 1, 7, 0,
        9, 4, 3, 0, 4, 0, 4, 0, 0, 7, 4, 3, 4, 8, 4, 4, 9, 7, 0, 7, 0, 3, 1, 2, 5, 1, 4, 2, 1, 0,
        8, 5, 4, 7, 1, 5, 2, 0, 2, 0, 0, 3, 7, 1, 7, 4, 2, 2, 4, 8, 5, 3, 5, 1, 5, 6, 2, 5, 7, 1,
        0, 5, 4, 2, 7, 3, 5, 7, 6, 0, 1, 0, 0, 1, 8, 5, 8, 7, 1, 1, 2, 4, 2, 6, 7, 5, 7, 8, 1, 2,
        5, 3, 5, 5, 2, 7, 1, 3, 6, 7, 8, 8, 0, 0, 5, 0, 0, 9, 2, 9, 3, 5, 5, 6, 2, 1, 3, 3, 7, 8,
        9, 0, 6, 2, 5, 1, 7, 7, 6, 3, 5, 6, 8, 3, 9, 4, 0, 0, 2, 5, 0, 4, 6, 4, 6, 7, 7, 8, 1, 0,
        6, 6, 8, 9, 4, 5, 3, 1, 2, 5, 8, 8, 8, 1, 7, 8, 4, 1, 9, 7, 0, 0, 1, 2, 5, 2, 3, 2, 3, 3,
        8, 9, 0, 5, 3, 3, 4, 4, 7, 2, 6, 5, 6, 2, 5, 4, 4, 4, 0, 8, 9, 2, 0, 9, 8, 5, 0, 0, 6, 2,
        6, 1, 6, 1, 6, 9, 4, 5, 2, 6, 6, 7, 2, 3, 6, 3, 2, 8, 1, 2, 5, 2, 2, 2, 0, 4, 4, 6, 0, 4,
        9, 2, 5, 0, 3, 1, 3, 0, 8, 0, 8, 4, 7, 2, 6, 3, 3, 3, 6, 1, 8, 1, 6, 4, 0, 6, 2, 5, 1, 1,
        1, 0, 2, 2, 3, 0, 2, 4, 6, 2, 5, 1, 5, 6, 5, 4, 0, 4, 2, 3, 6, 3, 1, 6, 6, 8, 0, 9, 0, 8,
        2, 0, 3, 1, 2, 5, 5, 5, 5, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5, 7, 8, 2, 7, 0, 2, 1, 1, 8, 1, 5,
        8, 3, 4, 0, 4, 5, 4, 1, 0, 1, 5, 6, 2, 5, 2, 7, 7, 5, 5, 5, 7, 5, 6, 1, 5, 6, 2, 8, 9, 1,
        3, 5, 1, 0, 5, 9, 0, 7, 9, 1, 7, 0, 2, 2, 7, 0, 5, 0, 7, 8, 1, 2, 5, 1, 3, 8, 7, 7, 7, 8,
        7, 8, 0, 7, 8, 1, 4, 4, 5, 6, 7, 5, 5, 2, 9, 5, 3, 9, 5, 8, 5, 1, 1, 3, 5, 2, 5, 3, 9, 0,
        6, 2, 5, 6, 9, 3, 8, 8, 9, 3, 9, 0, 3, 9, 0, 7, 2, 2, 8, 3, 7, 7, 6, 4, 7, 6, 9, 7, 9, 2,
        5, 5, 6, 7, 6, 2, 6, 9, 5, 3, 1, 2, 5, 3, 4, 6, 9, 4, 4, 6, 9, 5, 1, 9, 5, 3, 6, 1, 4, 1,
        8, 8, 8, 2, 3, 8, 4, 8, 9, 6, 2, 7, 8, 3, 8, 1, 3, 4, 7, 6, 5, 6, 2, 5, 1, 7, 3, 4, 7, 2,
        3, 4, 7, 5, 9, 7, 6, 8, 0, 7, 0, 9, 4, 4, 1, 1, 9, 2, 4, 4, 8, 1, 3, 9, 1, 9, 0, 6, 7, 3,
        8, 2, 8, 1, 2, 5, 8, 6, 7, 3, 6, 1, 7, 3, 7, 9, 8, 8, 4, 0, 3, 5, 4, 7, 2, 0, 5, 9, 6, 2,
        2, 4, 0, 6, 9, 5, 9, 5, 3, 3, 6, 9, 1, 4, 0, 6, 2, 5,
    ];

    shift &= 63;
    let x_a = TABLE[shift];
    let x_b = TABLE[shift + 1];
    let num_new_digits = (x_a >> 11) as _;
    let pow5_a = (0x7FF & x_a) as usize;
    let pow5_b = (0x7FF & x_b) as usize;
    let pow5 = &TABLE_POW5[pow5_a..];
    for (i, &p5) in pow5.iter().enumerate().take(pow5_b - pow5_a) {
        if i >= d.num_digits {
            return num_new_digits - 1;
        } else if d.digits[i] == p5 {
            continue;
        } else if d.digits[i] < p5 {
            return num_new_digits - 1;
        } else {
            return num_new_digits;
        }
    }
    num_new_digits
}

// https://doc.rust-lang.org/src/core/num/dec2flt/common.rs.html

/// Helper methods to process immutable bytes.
pub(crate) trait ByteSlice {
    /// Reads 8 bytes as a 64-bit integer in little-endian order.
    fn read_u64(&self) -> u64;

    /// Writes a 64-bit integer as 8 bytes in little-endian order.
    fn write_u64(&mut self, value: u64);

    /// Calculate the offset of a slice from another.
    fn offset_from(&self, other: &Self) -> isize;

    /// Iteratively parse and consume digits from bytes.
    /// Returns the same bytes with consumed digits being
    /// elided.
    fn parse_digits(&self, func: impl FnMut(u8)) -> &Self;
}

impl ByteSlice for [u8] {
    #[inline(always)] // inlining this is crucial to remove bound checks
    fn read_u64(&self) -> u64 {
        let mut tmp = [0; 8];
        tmp.copy_from_slice(&self[..8]);
        u64::from_le_bytes(tmp)
    }

    #[inline(always)] // inlining this is crucial to remove bound checks
    fn write_u64(&mut self, value: u64) {
        self[..8].copy_from_slice(&value.to_le_bytes())
    }

    #[inline]
    fn offset_from(&self, other: &Self) -> isize {
        other.len() as isize - self.len() as isize
    }

    #[inline]
    fn parse_digits(&self, mut func: impl FnMut(u8)) -> &Self {
        let mut s = self;

        while let Some((c, s_next)) = s.split_first() {
            let c = c.wrapping_sub(b'0');
            if c < 10 {
                func(c);
                s = s_next;
            } else {
                break;
            }
        }

        s
    }
}

/// Determine if 8 bytes are all decimal digits.
/// This does not care about the order in which the bytes were loaded.
pub(crate) fn is_8digits(v: u64) -> bool {
    let a = v.wrapping_add(0x4646_4646_4646_4646);
    let b = v.wrapping_sub(0x3030_3030_3030_3030);
    (a | b) & 0x8080_8080_8080_8080 == 0
}

/// A custom 64-bit floating point type, representing `f * 2^e`.
/// e is biased, so it be directly shifted into the exponent bits.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct BiasedFp {
    /// The significant digits.
    pub f: u64,
    /// The biased, binary exponent.
    pub e: i32,
}

impl BiasedFp {
    #[inline]
    pub const fn zero_pow2(e: i32) -> Self {
        Self { f: 0, e }
    }
}



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

    fn max_decimal_power() -> i32 {
        // Plus one to account for the fact that Decimal is formatted as 0.xxxeyyy
        (((1 << E) - B) as f64 * 2.0_f64.log10()).ceil() as i32 + 1
    }

    fn min_decimal_power() -> i32 {
        (-(B + M as i32) as f64 * 2.0_f64.log10()).floor() as i32
    }

    const fn qnan(negative: bool) -> Self {
        Semb {
            m: (1_usize << (M - 1)) as u128,
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

    // TODO: Is it correct to sub MINIMUM_EXPONENT for -B?
    // https://doc.rust-lang.org/src/core/num/dec2flt/slow.rs.html
    fn parse_long_mantissa<T: std::ops::Shr<usize> + std::ops::Shl<usize> + FromDecimal>(s: &[u8]) -> Self {
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
            s: 0
        }
        // BiasedFp { f: mantissa, e: power2 }
    }

    // https://doc.rust-lang.org/src/core/num/dec2flt/parse.rs.html
    /// Try to parse a special, non-finite float.
    pub fn parse_inf_nan(s: &[u8], negative: bool) -> Option<Self> {
        // Since a valid string has at most the length 8, we can load
        // all relevant characters into a u64 and work from there.
        // This also generates much better code.

        let mut register;
        let len: usize;

        // All valid strings are either of length 8 or 3.
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
            None => Ok(Self::parse_long_mantissa::<u128>(s))
        }
    }
}

pub type SembF16 = Semb<1, 5, 10, 15>;
pub type SembF32 = Semb<1, 8, 23, 127>;
pub type SembF64 = Semb<1, 11, 52, 1023>;
pub type SembF128 = Semb<1, 15, 112, 16383>;

#[cfg(test)]
mod semb_tests {
    use std::str::FromStr;
    use super::*;

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