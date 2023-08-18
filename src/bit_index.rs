pub use crate::bit_field::BitField;


/// Structure for accessing individual bits in any structure that implements [`BitIndexable`](crate::BitIndexable).
///
/// A [`BitIndex`](crate::BitIndex) can be used to address any singular bit in an array of up to `usize` bytes. 
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct BitIndex {
    byte_index: usize,
    bit_index: usize
}

impl BitIndex {

    /// Initialize a new [`BitIndex`](crate::BitIndex) that refers to the `bit_index` bit of
    /// the byte at `byte_index`. `bit_index` should be less than `8`
    pub fn new(byte_index: usize, bit_index: usize) -> BitIndex {
        BitIndex {byte_index, bit_index}
    }

    /// Access the bit index
    pub fn bit(&self) -> usize {
        self.bit_index
    }

    /// Returns the byte that this [`BitIndex`](crate::BitIndex) refers to.
    ///
    /// # Examples:
    ///
    /// ```rust
    /// use bitutils2::{BitIndex};
    ///
    /// let mut i = BitIndex::new(2, 3);
    /// assert_eq!(i.byte(), 2);
    /// i += 10;
    /// assert_eq!(i.byte(), 3);
    /// ```
    pub fn byte(&self) -> usize {
        self.byte_index
    }

    pub fn set_bit(&mut self, bit: usize) {
        self.bit_index = bit;
    }

    pub fn set_byte(&mut self, byte: usize) {
        self.byte_index = byte;
    }

    pub fn add_bits(&mut self, nbits: usize) {
        let bits = self.bit_index + nbits;
        self.bit_index = bits & 0x07;
        self.byte_index += bits >> 3;
    }
}

impl std::ops::Add for BitIndex {
    type Output = Self;

    fn add(self, other: Self) -> BitIndex {
        let bits = self.bit() + other.bit();
        BitIndex {
            byte_index: self.byte() + other.byte() + (bits >> 3),
            bit_index: bits & 0x07
        }
    }
}

impl std::ops::Sub for BitIndex {
    type Output = Self;

    fn sub(self, other: Self) -> BitIndex {
        if self.bit() >= other.bit() {
            BitIndex {
                byte_index: self.byte() - other.byte(),
                bit_index: self.bit() - other.bit()
            }
        } else {
            BitIndex {
                byte_index: self.byte() - other.byte() - 1,
                bit_index: (self.bit() + 8) - other.bit()
            }
        }
    }
}

impl std::ops::Add<usize> for BitIndex {
    type Output = Self;

    fn add(self, other: usize) -> BitIndex {
        let bits = self.bit() + other;
        BitIndex {
            byte_index: self.byte() + (bits >> 3),
            bit_index: bits & 0x07
        }
    }
}

impl std::ops::Add<&usize> for BitIndex {
    type Output = Self;

    fn add(self, other: &usize) -> BitIndex {
        let bits = self.bit() + other;
        BitIndex {
            byte_index: self.byte() + (bits >> 3),
            bit_index: bits & 0x07
        }
    }
}

impl std::ops::AddAssign<usize> for BitIndex {

    fn add_assign(&mut self, other: usize) {
        let bits = self.bit_index + other;
        self.bit_index = bits & 0x07;
        self.byte_index += bits >> 3;
    }
}

impl std::ops::AddAssign<&usize> for BitIndex {

    fn add_assign(&mut self, other: &usize) {
        let bits = self.bit_index + other;
        self.bit_index = bits & 0x07;
        self.byte_index += bits >> 3;
    }
}

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
        (self[index.byte()] & (0xf0 >> index.bit())) >> (7 - index.bit())
    }

    fn bit_slice(&self, start: &BitIndex, end: &BitIndex) -> BitField {
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
        if start_bit < end_bit {
            res.push((self[end_byte] >> (8 - end_bit)) << (start_bit + 8 - end_bit));
        } else if end_bit < start_bit {
            let res_len = res.len();
            let last = res[res_len - 1];
            res[res_len - 1] = (last >> (start_bit - end_bit)) << (start_bit - end_bit);
        }
        BitField::new(res, *end - *start)
    }

    fn max_index(&self) -> BitIndex {
        BitIndex::new(self.len(), 0)
    }
}

#[cfg(test)]
mod match_tests {
    use super::*;

    #[test]
    fn arithmetic() {
        assert_eq!(BitIndex::new(2, 3) + BitIndex::new(1, 3), BitIndex::new(3, 6));
        assert_eq!(BitIndex::new(0, 3) + BitIndex::new(4, 5), BitIndex::new(5, 0));
        assert_eq!(BitIndex::new(0, 6) + BitIndex::new(4, 5), BitIndex::new(5, 3));
        assert_eq!(BitIndex::new(3, 6) - BitIndex::new(1, 3), BitIndex::new(2, 3));
        assert_eq!(BitIndex::new(6, 3) - BitIndex::new(2, 3), BitIndex::new(4, 0));
        assert_eq!(BitIndex::new(3, 2) - BitIndex::new(1, 5), BitIndex::new(1, 5));
        assert_eq!(BitIndex::new(2, 2) - BitIndex::new(1, 6), BitIndex::new(0, 4))
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