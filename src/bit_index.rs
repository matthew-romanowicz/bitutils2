use std::str::FromStr;

pub use crate::bit_field::BitField;

/// Helper function for initializing [`BitIndex`](crate::BitIndex)
pub fn bx(bits: usize) -> BitIndex {
    BitIndex::new(bits >> 3, (bits & 0x07) as u8)
}


// #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
// pub struct BitIndex {
//     pub byte_index: usize,
//     pub bit_index: usize
// }

// impl BitIndex {

//     /// Initialize a new [`BitIndex`](crate::BitIndex) that refers to the `bit_index` bit of
//     /// the byte at `byte_index`. `bit_index` should be less than `8`
//     pub fn new(byte_index: usize, bit_index: usize) -> BitIndex {
//         BitIndex {byte_index, bit_index}
//     }

//     /// Returns the bit portion of this [`BitIndex`](crate::BitIndex).
//     pub fn bit(&self) -> usize {
//         self.bit_index
//     }

//     /// Returns the compliment of the bit portion of this [`BitIndex`](crate::BitIndex) (`8 - self.bit()`).
//     pub fn cbit(&self) -> usize {
//         8 - self.bit_index
//     }

//     /// Returns the byte portion of this [`BitIndex`](crate::BitIndex).
//     pub fn byte(&self) -> usize {
//         self.byte_index
//     }

//     /// Sets the bit portion of this [`BitIndex`](crate::BitIndex). `bit` must be less than `8`.
//     pub fn set_bit(&mut self, bit: usize) {
//         self.bit_index = bit;
//     }

//     /// Sets the byte portion of this [`BitIndex`](crate::BitIndex)
//     pub fn set_byte(&mut self, byte: usize) {
//         self.byte_index = byte;
//     }

//     /// Adds `nbits` bits to this [`BitIndex`](crate::BitIndex). The bit and byte portions will
//     /// be adjusted accordingly to ensure that the bit portion is always less than `8`
//     pub fn add_bits(&mut self, nbits: usize) {
//         let bits = self.bit_index + nbits;
//         self.bit_index = bits & 0x07;
//         self.byte_index += bits >> 3;
//     }
// }

// impl std::ops::Add for BitIndex {
//     type Output = Self;

//     fn add(self, other: Self) -> BitIndex {
//         let bits = self.bit() + other.bit();
//         BitIndex {
//             byte_index: self.byte() + other.byte() + (bits >> 3),
//             bit_index: bits & 0x07
//         }
//     }
// }

// impl std::ops::Sub for BitIndex {
//     type Output = Self;

//     fn sub(self, other: Self) -> BitIndex {
//         if self.bit() >= other.bit() {
//             BitIndex {
//                 byte_index: self.byte() - other.byte(),
//                 bit_index: self.bit() - other.bit()
//             }
//         } else {
//             BitIndex {
//                 byte_index: self.byte() - other.byte() - 1,
//                 bit_index: (self.bit() + 8) - other.bit()
//             }
//         }
//     }
// }

use std::ops::Neg;
use std::cmp::Ord;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sign {
    Negative,
    Positive,
}


impl std::ops::Neg for Sign {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Sign::Negative => Sign::Positive,
            Sign::Positive => Sign::Negative,
        }
    }
}

#[derive(Clone, Debug)]
enum BitIndexErrorKind {
    Empty,
    InvalidCharacter(usize),
    Overflow,
    UnitNotPresent
}

#[derive(Clone, Debug)]
pub struct ParseBitIndexError {
    kind: BitIndexErrorKind
}

impl ParseBitIndexError {
    fn new(kind: BitIndexErrorKind) -> ParseBitIndexError {
        ParseBitIndexError {kind}
    }
}

impl std::fmt::Display for ParseBitIndexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            BitIndexErrorKind::Empty => write!(f, "Input is empty"),
            BitIndexErrorKind::InvalidCharacter(i) => write!(f, "Invalid character encountered at position {}", i),
            BitIndexErrorKind::Overflow => write!(f, "Byte or bit value caused overflow"),
            BitIndexErrorKind::UnitNotPresent => write!(f, "No unit indicator (B and/or b) found in input"),
        }
    }    
}

/// Structure for accessing individual bits in any structure that implements [`BitIndexable`](crate::BitIndexable).
///
/// A [`BitIndex`](crate::BitIndex) can be used to address any singular bit in an array of up to `usize` bytes. 
/// This structure uses a `usize` to index the byte portion, and a separate `u8` to index the bit of the
/// selected byte. There is also a sign associated with this structure for arithmetic purposes. Attempting to
/// access a bit at a negative position will cause a panic.
/// 
/// # Examples
///
/// ```rust
/// use bitutils2::{BitIndex, BitIndexable};
///
/// let v = vec![0b01011100, 0b11001100];
/// //                ^               ^
/// //              (0,3)           (1,7)
///
/// let i = BitIndex::new(0, 3);
/// assert_eq!(v.bit_at(&i), 1);
///
/// let i = BitIndex::new(1, 7);
/// assert_eq!(v.bit_at(&i), 0);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitIndex {
    sign: Sign,
    byte: usize,
    bit: u8
}

impl BitIndex {

    pub const MAX: BitIndex = BitIndex {sign: Sign::Positive, byte: usize::MAX, bit: 7};
    pub const MIN: BitIndex = BitIndex {sign: Sign::Negative, byte: usize::MAX, bit: 7};

    /// Constructs a new [`BitIndex`](crate::BitIndex) with the specified `byte` and `bit` 
    /// values. The sign of the result is positive.
    pub fn new(byte: usize, bit: u8) -> BitIndex {
        BitIndex {sign: Sign::Positive, byte, bit}
    }

    /// Constructs a new [`BitIndex`](crate::BitIndex) with the specified `byte` value and `bit` 
    /// equal to zero. The sign of the result is positive.
    pub fn bytes(byte: usize) -> BitIndex {
        BitIndex::new(byte, 0)
    }

    /// Constructs a new [`BitIndex`](crate::BitIndex) with the specified `bit` value and `byte` 
    /// equal to zero. The sign of the result is positive.
    pub fn bits(bits: usize) -> BitIndex {
        BitIndex::new(bits >> 3, (bits & 0x07) as u8)
    }

    /// Constructs a new [`BitIndex`](crate::BitIndex) with `byte` and `bit` both equal to zero.
    pub fn zero() -> BitIndex {
        BitIndex::new(0, 0)
    }

    /// Returns true if the byte and bit indices are both zero, regardless of sign.
    pub fn is_zero(&self) -> bool {
        self.byte == 0 && self.bit == 0
    }

    /// Returns `true` if `self` is positive and `false` if self is zero or negative
    pub fn is_positive(&self) -> bool {
        matches!(self.sign, Sign::Positive) && !self.is_zero()
    }

    /// Returns `true` if `self` is negative and `false` if self is zero or positive
    pub fn is_negative(&self) -> bool {
        matches!(self.sign, Sign::Negative) && !self.is_zero()
    }

    /// Returns the bit portion of this [`BitIndex`](crate::BitIndex).
    pub fn byte(&self) -> usize {
        self.byte
    }

    /// Returns the bit portion of this [`BitIndex`](crate::BitIndex).
    pub fn bit(&self) -> u8 {
        self.bit
    }

    /// Returns the compliment of the bit portion of this [`BitIndex`](crate::BitIndex) (`8 - self.bit()`).
    pub fn cbit(&self) -> u8 {
        8 - self.bit
    }

    /// Sets the bit portion of this [`BitIndex`](crate::BitIndex). `bit` must be less than `8`.
    pub fn set_bit(&mut self, bit: u8) {
        self.bit = bit;
    }

    /// Sets the byte portion of this [`BitIndex`](crate::BitIndex)
    pub fn set_byte(&mut self, byte: usize) {
        self.byte = byte;
    }

    /// Adds `nbits` bits to this [`BitIndex`](crate::BitIndex). The bit and byte portions will
    /// be adjusted accordingly to ensure that the bit portion is always less than `8`
    pub fn add_bits(&mut self, nbits: usize) {
        *self = *self + nbits;
    }

    pub fn from_i64_bytes(byte: i64) -> BitIndex {
        if byte < 0 {
            BitIndex {
                sign: Sign::Negative,
                byte: byte.abs() as usize,
                bit: 0
            }
        } else {
            BitIndex {
                sign: Sign::Positive,
                byte: byte as usize,
                bit: 0
            }
        }
    }

    /// Calculates the smallest non-negative value `b` such that `self + b = n * rhs` where `n` 
    /// is an integer. 
    pub fn rem_euclid(&self, rhs: &BitIndex) -> BitIndex {
        let mut lhs_total_bits = self.byte as i128 * 8 + self.bit as i128;
        let mut rhs_total_bits = rhs.byte as i128 * 8 + rhs.bit as i128;

        if matches!(self.sign, Sign::Negative) {
            lhs_total_bits *= -1;
        }

        if matches!(rhs.sign, Sign::Negative) {
            rhs_total_bits *= -1;
        }

        let mut total_bits = lhs_total_bits.rem_euclid(rhs_total_bits);
        if total_bits < 0 {
            total_bits *= -1;
            -BitIndex::new((total_bits >> 3) as usize, (total_bits & 0x07) as u8)
        } else {
            BitIndex::new((total_bits >> 3) as usize, (total_bits & 0x07) as u8)
        }

    }
}


impl FromStr for BitIndex {
    type Err = ParseBitIndexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut char_iter = s.char_indices().peekable();

        let sign = match char_iter.peek() {
            None => return Err(ParseBitIndexError{kind: BitIndexErrorKind::Empty}),
            Some((_, '-')) => {
                char_iter.next();
                Sign::Negative
            },
            Some((_, '+')) => {
                char_iter.next();
                Sign::Positive
            },
            Some(_) => Sign::Positive
        };

        let mut numeral_found = false;
        let mut b_found = false;
        let mut byte: usize = 0;
        let mut bit: usize = 0;
        let mut acc: usize = 0;
        while let Some((i, ch)) = char_iter.next() {
            match ch {
                '0'..='9' => {
                    acc = acc.checked_mul(10).ok_or(ParseBitIndexError{kind: BitIndexErrorKind::Overflow})?;
                    acc = acc.checked_add(ch as usize - 48).ok_or(ParseBitIndexError{kind: BitIndexErrorKind::Overflow})?;
                    numeral_found = true;
                },
                'B' if numeral_found && !b_found => {
                    b_found = true;
                    numeral_found = false;
                    byte = acc;
                    acc = 0;
                },
                'b' if numeral_found => {
                    b_found = true;
                    bit = acc;
                    break;
                },
                _ => {
                    return Err(ParseBitIndexError{kind: BitIndexErrorKind::InvalidCharacter(i)});
                }

            }
        }

        if let Some((i, _)) = char_iter.next() {
            Err(ParseBitIndexError{kind: BitIndexErrorKind::InvalidCharacter(i)})
        } else if !b_found {
            Err(ParseBitIndexError{kind: BitIndexErrorKind::UnitNotPresent})
        } else {
            byte = byte.checked_add(bit >> 3).ok_or(ParseBitIndexError{kind: BitIndexErrorKind::Overflow})?;
            let bit = (bit & 0b111) as u8;

            Ok(BitIndex{sign, byte, bit})
        }

    }
}

impl std::cmp::PartialOrd for BitIndex {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::cmp::Ord for BitIndex {
    fn cmp(&self, other: &BitIndex) -> std::cmp::Ordering {
        match (&self.sign, &other.sign) {
            (Sign::Positive, Sign::Positive) => {
                match self.byte.cmp(&other.byte) {
                    std::cmp::Ordering::Equal => {
                        self.bit.cmp(&other.bit)
                    },
                    other_cmp => other_cmp
                }
            },
            (Sign::Positive, Sign::Negative) => {
                std::cmp::Ordering::Greater
            },
            (Sign::Negative, Sign::Negative) => {
                std::cmp::Ordering::Less
            },
            (Sign::Negative, Sign::Positive) => {
                (-self).cmp(&-other).reverse()
            }
        }
    }
}

impl std::ops::Neg for BitIndex {
    type Output = BitIndex;
    fn neg(self) -> Self::Output {
        BitIndex {
            sign: -self.sign, 
            byte: self.byte, 
            bit: self.bit
        }
    }
}

impl std::ops::Neg for &BitIndex {
    type Output = BitIndex;
    fn neg(self) -> Self::Output {
        BitIndex {
            sign: -self.sign.clone(), 
            byte: self.byte, 
            bit: self.bit
        }
    }
}

impl std::ops::Add<BitIndex> for BitIndex {
    type Output = BitIndex;
    fn add(self, rhs: BitIndex) -> Self::Output {
        match (&self.sign, &rhs.sign) {
            (Sign::Positive, Sign::Positive) => {
                let bits = self.bit as usize + rhs.bit as usize;
                BitIndex::new(self.byte + rhs.byte + bits / 8, (bits % 8) as u8)
            },
            (Sign::Positive, Sign::Negative) => {
                // 5B2b - 4B3b
                let bits = self.bit as i64 - rhs.bit as i64;
                let mut lhs_byte = self.byte;
                let mut rhs_byte = rhs.byte;
                if bits >= 0 {
                    lhs_byte += bits as usize / 8;
                } else {
                    rhs_byte += bits.abs() as usize / 8;
                };

                if lhs_byte > rhs_byte {
                    if bits >= 0 {
                        BitIndex::new(lhs_byte - rhs_byte, (bits % 8) as u8)
                    } else {
                        BitIndex::new(lhs_byte - rhs_byte - 1, ((bits + 8) % 8) as u8)
                    }
                    
                } else if lhs_byte < rhs_byte {
                    if bits <= 0 {
                        -BitIndex::new(rhs_byte - lhs_byte, (bits.abs() % 8) as u8)
                    } else {
                        -BitIndex::new(rhs_byte - (lhs_byte + 1), ((bits - 8).abs() % 8) as u8)
                    }
                } else {
                    if bits < 0 {
                        -BitIndex::new(0, (bits.abs() % 8) as u8)
                    } else {
                        BitIndex::new(0, (bits % 8) as u8)
                    }
                }
            },
            (Sign::Negative, Sign::Negative) => {
                (self.neg() + rhs.neg()).neg()
            },
            (Sign::Negative, Sign::Positive) => {
                (self.neg() + rhs.neg()).neg()
            },
        }
        
    }
}

impl std::ops::Sub<BitIndex> for BitIndex {
    type Output = BitIndex;
    fn sub(self, rhs: BitIndex) -> Self::Output {
        self + -rhs
        
    }
}

impl<'a, 'b> std::ops::Add<&'a BitIndex> for &'b BitIndex {
    type Output = BitIndex;
    fn add(self, rhs: &'a BitIndex) -> Self::Output {
        self.clone() + rhs.clone()
        
    }
}

impl<'a, 'b> std::ops::Sub<&'a BitIndex> for &'b BitIndex {
    type Output = BitIndex;
    fn sub(self, rhs: &'a BitIndex) -> Self::Output {
        self.clone() + (-rhs).clone()
        
    }
}

impl std::ops::Add<usize> for BitIndex {
    type Output = Self;

    fn add(self, other: usize) -> BitIndex {
        return self + BitIndex::bits(other as usize)
    }
}

impl std::ops::Add<&usize> for BitIndex {
    type Output = Self;

    fn add(self, other: &usize) -> BitIndex {
        return self + BitIndex::bits(*other as usize)
    }
}

// impl std::ops::Add<usize> for BitIndex {
//     type Output = Self;

//     fn add(self, other: usize) -> BitIndex {
//         let bits = self.bit() + other;
//         BitIndex {
//             byte_index: self.byte() + (bits >> 3),
//             bit_index: bits & 0x07
//         }
//     }
// }

// impl std::ops::Add<&usize> for BitIndex {
//     type Output = Self;

//     fn add(self, other: &usize) -> BitIndex {
//         let bits = self.bit() + other;
//         BitIndex {
//             byte_index: self.byte() + (bits >> 3),
//             bit_index: bits & 0x07
//         }
//     }
// }

impl std::ops::AddAssign<usize> for BitIndex {

    fn add_assign(&mut self, other: usize) {
        *self = *self + other
    }
}

impl std::ops::AddAssign<&usize> for BitIndex {

    fn add_assign(&mut self, other: &usize) {
        *self = *self + other
    }
}

// impl std::ops::AddAssign<usize> for BitIndex {

//     fn add_assign(&mut self, other: usize) {
//         let bits = self.bit_index + other;
//         self.bit_index = bits & 0x07;
//         self.byte_index += bits >> 3;
//     }
// }

// impl std::ops::AddAssign<&usize> for BitIndex {

//     fn add_assign(&mut self, other: &usize) {
//         let bits = self.bit_index + other;
//         self.bit_index = bits & 0x07;
//         self.byte_index += bits >> 3;
//     }
// }

pub trait BitIndexable {

    /// Get the bit at the given bit index. Returns a `u8` instead of a `bool` to accommodate 
    /// operations such as bitshifts on the result, but this function should always return either `0` or `1`.
    fn bit_at(&self, index: &BitIndex) -> u8;

    fn bit_slice(&self, start: &BitIndex, end: &BitIndex) -> BitField;

    /// Get the bit index that is equivalent to the length of the structure (accessing at this index 
    /// is out of bounds, but any index below this is allowed)
    fn max_index(&self) -> BitIndex;
}

impl<T: BitIndexable> BitIndexable for &T {
    fn bit_at(&self, index: &BitIndex) -> u8 {
        (*self).bit_at(index)
    }

    fn bit_slice(&self, start: &BitIndex, end: &BitIndex) -> BitField {
        (*self).bit_slice(start, end)
    }

    fn max_index(&self) -> BitIndex {
        (*self).max_index()
    }
}

impl BitIndexable for Vec<u8> {

    fn bit_at(&self, index: &BitIndex) -> u8 {
        if index.is_negative() {
            panic!("Bit index underflow")
        }
        (self[index.byte()] & (0xf0 >> index.bit())) >> (7 - index.bit())
    }

    fn bit_slice(&self, start: &BitIndex, end: &BitIndex) -> BitField {
        if start.is_negative() || end.is_negative() {
            panic!("Bit index underflow")
        }
        // This is the same implementation as the BitField bit_slice method. If you change this, consider changing the other one
        let start_byte = start.byte();
        let start_bit = start.bit();
        let end_byte = end.byte();
        let end_bit = end.bit();

        let mut res = Vec::<u8>::new();

        if start_bit == 0 {
            res = self[start_byte..end_byte].to_vec();
        } else {
            for i in start_byte..end_byte {
                let carry = if i + 1 < self.len() {self[i+1] >> (8 - start_bit)} else {0};
                res.push((self[i] << start_bit) | carry);
            }
        }
        match start_bit.cmp(&end_bit) {
            std::cmp::Ordering::Greater => {
                let res_len = res.len();
                let last = res[res_len - 1];
                res[res_len - 1] = (last >> (start_bit - end_bit)) << (start_bit - end_bit);
            },
            std::cmp::Ordering::Less => {
                res.push((self[end_byte] >> (8 - end_bit)) << (start_bit + 8 - end_bit));
            },
            _ => ()
        }
        BitField::new(res, *end - *start)
    }

    fn max_index(&self) -> BitIndex {
        BitIndex::new(self.len(), 0)
    }
}

#[cfg(test)]
mod bit_index_tests {
    use super::*;

    #[test]
    fn parse_test() {
        assert_eq!(BitIndex::new(15, 4), BitIndex::from_str("15B4b").unwrap());
        assert_eq!(BitIndex::new(1300, 4), BitIndex::from_str("1300B4b").unwrap());
        assert_eq!(BitIndex::new(0, 4), BitIndex::from_str("4b").unwrap());
        assert_eq!(BitIndex::new(5, 5), BitIndex::from_str("45b").unwrap());
        assert_eq!(BitIndex::new(4, 0), BitIndex::from_str("4B").unwrap());
        assert_eq!(BitIndex::new(0, 0), BitIndex::from_str("0B").unwrap());
        assert_eq!(BitIndex::new(15, 3), BitIndex::from_str("10B43b").unwrap());
        assert_eq!(-BitIndex::new(15, 3), BitIndex::from_str("-10B43b").unwrap());
        assert_eq!(BitIndex::new(15, 3), BitIndex::from_str("+10B43b").unwrap());

        let max_case = format!("{}B{}b", usize::MAX, 7);
        assert_eq!(BitIndex::new(usize::MAX, 7), BitIndex::from_str(&max_case).unwrap());
    }

    #[test]
    fn parse_errors_test() {
        // Empty input
        let err_kind = BitIndex::from_str("").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::Empty));

        // Input without units
        let err_kind = BitIndex::from_str("23").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::UnitNotPresent));

        // Overflow in byte value
        let overflow_1 = format!("{}B{}b", usize::MAX as u128 + 1, 0);
        let err_kind = BitIndex::from_str(&overflow_1).unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::Overflow));

        // Overflow in bit value
        let overflow_2 = format!("{}B{}b", 0, usize::MAX as u128 * 8 + 1);
        let err_kind = BitIndex::from_str(&overflow_2).unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::Overflow));

        // Overflow in byte value after carrying bits
        let overflow_3 = format!("{}B{}b", usize::MAX, 8);
        let err_kind = BitIndex::from_str(&overflow_3).unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::Overflow));

        // Invalid character in various locations
        let err_kind = BitIndex::from_str("1xB43b").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(1)));
        let err_kind = BitIndex::from_str("10BB43b").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(3)));
        let err_kind = BitIndex::from_str("10B4x3b").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(4)));
        let err_kind = BitIndex::from_str("10B43b_").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(6)));
        let err_kind = BitIndex::from_str("10B43B").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(5)));
        let err_kind = BitIndex::from_str("10b43B").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(3)));
        let err_kind = BitIndex::from_str("B43b").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(0)));
        let err_kind = BitIndex::from_str("b").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(0)));
        let err_kind = BitIndex::from_str("10Bb").unwrap_err().kind;
        assert!(matches!(err_kind, BitIndexErrorKind::InvalidCharacter(3)));
    }

        #[test]
    fn add_test() {
        assert_eq!(BitIndex::new(2, 3) + BitIndex::new(1, 3), BitIndex::new(3, 6));
        assert_eq!(BitIndex::new(0, 3) + BitIndex::new(4, 5), BitIndex::new(5, 0));
        assert_eq!(BitIndex::new(0, 6) + BitIndex::new(4, 5), BitIndex::new(5, 3));
        assert_eq!(BitIndex::new(5, 1) + BitIndex::new(3, 2), BitIndex::new(8, 3));
        assert_eq!(BitIndex::new(5, 1) + BitIndex::new(3, 7), BitIndex::new(9, 0));
        assert_eq!(BitIndex::new(5, 3) + BitIndex::new(3, 7), BitIndex::new(9, 2));
    }

    #[test]
    fn sub_test() {
        assert_eq!(BitIndex::new(3, 6) - BitIndex::new(1, 3), BitIndex::new(2, 3));
        assert_eq!(BitIndex::new(6, 3) - BitIndex::new(2, 3), BitIndex::new(4, 0));
        assert_eq!(BitIndex::new(3, 2) - BitIndex::new(1, 5), BitIndex::new(1, 5));
        assert_eq!(BitIndex::new(2, 2) - BitIndex::new(1, 6), BitIndex::new(0, 4));
        assert_eq!(BitIndex::new(5, 1) - BitIndex::new(3, 2), BitIndex::new(1, 7));
        assert_eq!(BitIndex::new(5, 5) - BitIndex::new(5, 2), BitIndex::new(0, 3));
        assert_eq!(BitIndex::new(5, 2) - BitIndex::new(5, 5), -BitIndex::new(0, 3));
        assert_eq!(BitIndex::new(3, 2) - BitIndex::new(5, 5), -BitIndex::new(2, 3));
        assert_eq!(BitIndex::new(3, 5) - BitIndex::new(5, 3), -BitIndex::new(1, 6));
    }

    #[test]
    fn rem_euclid_test() {
        assert_eq!(BitIndex::new(3, 6).rem_euclid(&BitIndex::new(1, 3)), BitIndex::new(1, 0));
        assert_eq!(BitIndex::new(6, 3).rem_euclid(&BitIndex::new(2, 3)), BitIndex::new(1, 5));
        assert_eq!(BitIndex::new(3, 2).rem_euclid(&BitIndex::new(1, 5)), BitIndex::zero());
        assert_eq!(BitIndex::new(2, 2).rem_euclid(&BitIndex::new(1, 6)), BitIndex::new(0, 4));
        assert_eq!((-BitIndex::new(3, 6)).rem_euclid(&BitIndex::new(1, 3)), BitIndex::new(0, 3));
        assert_eq!((-BitIndex::new(6, 3)).rem_euclid(&BitIndex::new(2, 3)), BitIndex::new(0, 6));
        assert_eq!((-BitIndex::new(3, 2)).rem_euclid(&BitIndex::new(1, 5)), BitIndex::zero());
        assert_eq!((-BitIndex::new(2, 2)).rem_euclid(&BitIndex::new(1, 6)), BitIndex::new(1, 2));
    }

    #[test]
    fn comparisons() {
        assert!(BitIndex::new(5, 4) == BitIndex::new(5, 4));
        assert!(BitIndex::new(5, 4) <= BitIndex::new(5, 4));
        assert!(BitIndex::new(5, 4) >= BitIndex::new(5, 4));
        assert!(BitIndex::new(5, 4) != BitIndex::new(6, 3));
        assert!(BitIndex::new(6, 4) != BitIndex::new(6, 3));
        assert!(BitIndex::new(5, 4) < BitIndex::new(6, 3));
        assert!(BitIndex::new(5, 4) <= BitIndex::new(6, 3));
        assert!(BitIndex::new(5, 4) < BitIndex::new(6, 3));
        assert!(BitIndex::new(6, 4) > BitIndex::new(6, 3));
        assert!(BitIndex::new(6, 4) >= BitIndex::new(6, 3));

        assert!(BitIndex::new(6, 4) + 1 == BitIndex::new(6, 5));
        assert!(BitIndex::new(6, 4) + 12 == BitIndex::new(8, 0));
        assert!(BitIndex::new(6, 4) + BitIndex::new(0, 4) == BitIndex::new(7, 0));
        assert!(BitIndex::new(6, 4) + BitIndex::new(2, 7) == BitIndex::new(9, 3));
    }

    #[test]
    fn indexing_u8() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        let mut index = BitIndex::new(0, 0);
        assert_eq!(v.bit_at(&index), 0);
        index += 1;
        assert_eq!(v.bit_at(&index), 1);
        index += 1;
        assert_eq!(v.bit_at(&index), 0);
        index += 5;
        assert_eq!(v.bit_at(&index), 1);
        index += 4;
        assert_eq!(v.bit_at(&index), 1);
        index += 1;
        assert_eq!(v.bit_at(&index), 0);
        index += 9;
        assert_eq!(v.bit_at(&index), 1);
        index += 1;
        assert_eq!(v.bit_at(&index), 1);
    }
}