use crate::bit_index::{BitIndex, BitIndexable};

/// Represents a finite array of contiguous bits that supports several operations such as 
/// indexing, slicing, shifting, etc.
///
/// The [`BitField`](crate::BitField) structure stores the bits packed in an array of bytes 
/// for memory efficiency, but attempts to make this mostly unapparant in the API. When a 
/// singular bit is accessed, it is returned as a u8 (either 0x00 or 0x01) to facilitate 
/// performing bitwise operations with the result. 
///
/// # Examples
/// ### Constructors
///```rust
/// use bitutils2::{BitField, BitIndex};
///
/// // Returns a bitfield with 0001 0010 0011 0100 0100 0101 0000 0000 
/// let bf1 = BitField::new(vec![0x12, 0x34, 0x45, 0x00], BitIndex::new(4, 0));
/// // Returns a bitfield with 0001 0010 0011 0100 0100 0101 00. The bytes represented by the
/// // vector are clipped to the bit index provided.
/// let bf2 = BitField::new(vec![0x12, 0x34, 0x45, 0x00], BitIndex::new(3, 2));
///
/// // Returns the same bitfield as 'bf1' but automatically infers the length from 
/// // the provided vec. This constructor cannot be used to produce a bit field that 
/// // does not end on a byte boundary like 'bf2'
/// let bf3 = BitField::from_vec(vec![0x12, 0x34, 0x45, 0x00]);
///
/// assert_eq!(bf1, bf3);
/// assert_ne!(bf1, bf2); // bf1 and bf3 are not equal because they have different lengths
///
/// 
/// // Returns a bitfield with 0001 0010 0011 0100 0100 0101 00 and an inferred length
/// // of 3 bytes and 2 bits. This constructor can be used to create a bitfield of
/// // any length. Spaces or underscores can be used anywhere in the input and are
/// // ignored by the constructor.
/// let bf4 = BitField::from_bin_str("0001 0010 0011 0100 0100 0101 00");
///
/// // bf5 has the same contents as bf4 but is two bits longer
/// let bf5 = BitField::from_bin_str("0001 0010 0011 0100 0100 0101 0000");
///
/// assert_eq!(bf2, bf4); // bf2 and bf4 are equal in both length and contents
/// assert_ne!(bf4, bf5); // bf4 and bf5 are not equal because they have different lengths
///
/// // Returns a bitfield with 0001 0010 0011 0100 0100 0101 0000 and an inferred length
/// // of 3 bytes and 4 bits. This constructor can only be used to create bitfields witg
/// // lengths that end on nibble boundaries. Spaces or underscores can be used anywhere 
/// // in the input and are ignored by the constructor.
/// let bf6 = BitField::from_hex_str("12 34 45 0");
///
/// // bf7 has the same contents as bf6 but is four bits (one nibble) longer
/// let bf7 = BitField::from_hex_str("12 34 45 00");
///
/// assert_eq!(bf5, bf6); // bf5 and bf6 are equal in both length and contents
/// assert_eq!(bf3, bf7); // bf3 and bf7 are equal in both length and contents
///
/// // Returns a bitfield with 5 bytes of 0x00
/// let bf8 = BitField::zeros(&BitIndex::new(5, 0));
///
/// 
///```
/// ### Bitwise AND, OR, XOR, and NOT
///
/// The common bitwise operations (AND, OR, XOR) are supported. If the two sides have the same
/// length, then the operation is applied to every bit in the arguments and the resulting 
/// [`BitField`](crate::BitField) is returned. If the two sides have different lengths, then
/// The operation is only applied to bits up to the shortest length and the resulting 
/// [`BitField`](crate::BitField) is returned.
///
///```rust
/// use bitutils2::{BitField, BitIndex};
///
/// // Initializing two bitfields that have the same length, and one that is much shorter
/// let bf1 = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
/// let bf2 = BitField::from_bin_str("0101 0000 1100 0111 1010 1111 0001");
/// let bf3 = BitField::from_bin_str("0101 0000 1100 01");
///
/// // Bitwise AND (&)
/// assert_eq!(&bf1 & &bf2, BitField::from_bin_str("0001 0000 0000 0111 1000 0101 0001"));
/// assert_eq!(&bf1 & &bf3, BitField::from_bin_str("0001 0000 0000 01"));
///
/// // Bitwise OR (|)
/// assert_eq!(&bf1 | &bf2, BitField::from_bin_str("0111 1010 1100 1111 1110 1111 0111"));
/// assert_eq!(&bf1 | &bf3, BitField::from_bin_str("0111 1010 1100 11"));
///
/// // Bitwise XOR (^)
/// assert_eq!(&bf1 ^ &bf2, BitField::from_bin_str("0110 1010 1100 1000 0110 1010 0110"));
/// assert_eq!(&bf1 ^ &bf3, BitField::from_bin_str("0110 1010 1100 10"));
///
/// // Bitwise NOT (!)
/// assert_eq!(!&bf1, BitField::from_bin_str("1100 0101 1111 0000 0011 1010 1000"));
/// assert_eq!(!&bf2, BitField::from_bin_str("1010 1111 0011 1000 0101 0000 1110"));
/// assert_eq!(!&bf3, BitField::from_bin_str("1010 1111 0011 10"));
///```
#[derive(Clone, Debug)]
pub struct BitField {
    v: Vec<u8>,
    length: BitIndex
}

impl BitField {

    /// Returns a new [`BitField`](crate::BitField) structure with the contents of the vector `v` 
    /// interpreted as bytes and the length `length` in bits. If the length does not lie on a 
    /// byte boundary, it is expected that the vector will have a final element that specifies
    /// the remaining bits.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf = BitField::new(vec![0b11001100, 0b01010101, 0b00110000], BitIndex::new(2, 4));
    /// assert_eq!(bf, BitField::from_bin_str("1100 1100 0101 0101 0011"));
    ///
    /// let bf = BitField::new(vec![0b11001100, 0b01010101, 0b00110000], BitIndex::new(3, 0));
    /// assert_eq!(bf, BitField::from_bin_str("1100 1100 0101 0101 0011 0000"));
    ///```
    pub fn new(v: Vec<u8>, length: BitIndex) -> BitField {
        BitField {v, length}
    }

    /// Returns a [`BitField`](crate::BitField) structure with the contents of the vector 'v'.
    ///
    /// The length of the bitfield is automatically calculated as the number of bits in the
    /// input vector. To create a [`BitField`](crate::BitField) that is not an integral 
    /// number of bytes long, use the [`new`](crate::BitField::new) constructor.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf = BitField::from_vec(vec![0x00, 0xab, 0xff]);
    /// assert_eq!(bf.len(), BitIndex::new(3, 0));
    /// assert_eq!(bf, BitField::from_bin_str("0000 0000 1010 1011 1111 1111"));
    ///```
    pub fn from_vec(v: Vec<u8>) -> BitField {
        let length = BitIndex::new(v.len(), 0);
        BitField {v, length}
    }

    /// Creates and returns a [`BitField`](crate::BitField) of zeros (0x00) with the given length.
    pub fn zeros(length: &BitIndex) -> BitField {
        let mut v = Vec::<u8>::new();
        let end = if length.bit() == 0 {length.byte()} else {length.byte() + 1};
        v.resize(end, 0);
        BitField {v, length: *length}
    }

    /// Creates and returns a [`BitField`](crate::BitField) of ones (0xFF) with the given length.
    pub fn ones(length: &BitIndex) -> BitField {
        let mut v = Vec::<u8>::new();
        if length.bit() == 0 {
            v.resize(length.byte(), 0xff);
        } else {
            v.resize(length.byte() + 1, 0xff);
            let last = (v[length.byte()] >> length.cbit()) << length.cbit();
            v[length.byte()] = last;
        }
        BitField {v, length: *length}
    }

    /// Parses a [`BitField`](crate::BitField) from a `str` of ones and zeros. Underscores and
    /// spaces are allowed and are ignored. Any other character will cause a panic.
    pub fn from_bin_str(s: &str) -> BitField {
        let mut length = BitIndex::new(0, 0);
        let mut byte = 0;
        let mut v = Vec::<u8>::new();
        for c in s.chars() {
            match c {
                '0' => {
                    length += 1;
                },
                '1' => {
                    byte += 0x01 << (7 - length.bit());
                    length += 1;
                },
                ' ' | '_' => continue,
                _ => panic!("Encountered unexpected character when parsing binary: '{}'", c)
            }
            if length.bit() == 0 {
                v.push(byte);
                byte = 0;
            }
        }
        if length.bit() != 0 {
            v.push(byte);
        }
        BitField {v, length}
    }

    /// Parses a [`BitField`](crate::BitField) from a `str` of hex characters (0-9, a-f, or A-F). 
    /// Underscores and spaces are allowed and are ignored. Any other character will cause a panic.
    pub fn from_hex_str(s: &str) -> BitField {
        let mut buffer = Vec::<u8>::new();
        let mut left = true;
        let mut n: u8 = 0;
        for c in s.chars() {
            match c {
                '0'..='9' => {
                    if left {
                        n = ((c as u8) -  48) << 4;
                    } else {
                        buffer.push(n + ((c as u8) -  48));
                        n = 0;
                    }
                },
                'a'..='f' => {
                    if left {
                        n = ((c as u8) -  87) << 4;
                    } else {
                        buffer.push(n + ((c as u8) -  87));
                        n = 0;
                    }
                },
                'A'..='F' => {
                    if left {
                        n = ((c as u8) -  55) << 4;
                    } else {
                        buffer.push(n + ((c as u8) -  55));
                        n = 0;
                    }
                },
                '_' | ' ' => continue,
                _ => panic!("Encountered unexpected character when parsing hex: '{}'", c)
            }
            left = !left;
        }

        let length = if left {
            BitIndex::new(buffer.len(), 0)
        } else {
            buffer.push(n);
            BitIndex::new(buffer.len() - 1, 4)
        };

        BitField {v: buffer, length}
    }

    /// Returns the length of the [`BitField`](crate::BitField) as a [`BitIndex`](crate::BitIndex).
    pub fn len(&self) -> BitIndex {
        self.length
    }

    /// Deletes the contents of the [`BitField`](crate::BitField) and sets the length to 0.
    pub fn clear(&mut self) {
        self.v.clear();
        self.length = BitIndex::new(0, 0);
    }

    /// Truncates the [`BitField`](crate::BitField) to `new_length` if `new_length` is shorter than 
    /// the current length. Does nothing otherwise.
    pub fn truncate(&mut self, new_length: &BitIndex) {
        if self.length <= *new_length {
            return
        }
        if new_length.bit() == 0 {
            self.v.truncate(new_length.byte());
        } else {
            self.v.truncate(new_length.byte() + 1);
            let last = (self.v[new_length.byte()] >> new_length.cbit()) << new_length.cbit();
            self.v[new_length.byte()] = last;
        }
        self.length = *new_length;
    }

    /// Concatenates the argument onto the end of the [`BitField`](crate::BitField), adjusting the 
    /// length of the [`BitField`](crate::BitField) accordingly.
    pub fn extend(&mut self, other: &BitField) {
        if self.length.bit() == 0 {
            self.v.extend(other.v.clone());
        } else {
            let cbit = self.length.cbit();
            self.v[self.length.byte()] |= other.v[0] >> self.length.bit();
            let mut carry = other.v[0] << cbit;
            let end = if other.length.bit() == 0 {other.length.byte()} else {other.length.byte() + 1};
            for i in 1..end {
                self.v.push((other.v[i] >> self.length.bit()) | carry);
                carry = other.v[i] << cbit;
            }
            if (self.length.bit() + other.length.bit() > 8) || (other.length.bit() == 0) {
                self.v.push(carry);
            }
        
        }
        self.length = self.length + other.length;
    }

    /// Repeats a bitfiled `n` times. If `n` is `0`, the bitfield is cleared and if `n` is 1, the bitfield
    /// is unmodified. Otherwise, the bitfield is extended such that it's contents repeat `n` times and its
    /// length is multiplied by `n`.
    pub fn repeat(&mut self, n: usize) {
        match n {
            0 => self.clear(),
            1 => (),
            _ => {
                let extra = self.clone();
                for _ in 0..(n - 1) {
                    self.extend(&extra);
                }
            }
        }
    }

    pub fn extract_u8(&self, start: BitIndex) -> u8 {
        if start.bit() == 0 {
            self.v[start.byte()]
        } else {
            (self.v[start.byte()] << start.bit()) | (self.v[start.byte() + 1] >> start.cbit())
        }
    }

}

impl BitIndexable for BitField {
    fn bit_at(&self, index: &BitIndex) -> u8 {
        (self.v[index.byte()] >> (7 - index.bit())) & 0x01
    }

    fn bit_slice(&self, start: &BitIndex, end: &BitIndex) -> BitField {
        // This is the same implementation as the Vec<u8> bit_slice method. If you change this, consider changing the other one
        let start_byte = start.byte();
        let start_bit = start.bit();
        let start_cbit = start.cbit();
        let end_byte = end.byte();
        let end_bit = end.bit();
        let end_cbit = end.cbit();

        let mut res = Vec::<u8>::new();

        if start_bit == 0 {
            res = self.v[start_byte..end_byte].to_vec();
        } else {
            for i in start_byte..end_byte {
                let carry = if i + 1 < self.v.len() {self.v[i+1] >> start_cbit} else {0};
                println!("{} {}", i, carry);
                res.push((self.v[i] << start_bit) | carry);
            }
        }
        match start_bit.cmp(&end_bit) {
            std::cmp::Ordering::Greater => {
                let res_len = res.len();
                let last = res[res_len - 1];
                res[res_len - 1] = (last >> (start_bit - end_bit)) << (start_bit - end_bit);
            },
            std::cmp::Ordering::Less => {
                res.push((self.v[end_byte] >> end_cbit) << (start_bit + end_cbit));
            },
            _ => ()
        }
        BitField {v: res, length: *end - *start}
    }

    fn max_index(&self) -> BitIndex {
        self.length
    }
}

impl std::cmp::PartialEq for BitField {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            false
        } else if self.len().bit() == 0 {
            self.v == other.v
        } else {
            let n = self.length.byte();
            if self.v[0..n] != other.v[0..n] {
                return false
            }
            let m = if cfg!(test) { // If testing, verify all bits, even the ones past the end of the "final" bit
                0
            } else {
                self.len().cbit()
            };
            (self.v[n] >> m) == (other.v[n] >> m)
        }
    }
}

impl std::cmp::Eq for BitField {}

impl std::ops::BitAnd for &BitField  {
    type Output = BitField;

    /// Returns the bitwise `&` operation on the two inputs. If the two inputs have different lengths,
    /// then the returned value will have the length of the shortest input.
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf1 = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
    /// let bf2 = BitField::from_bin_str("0101 0000 1100 0111 1010 1111 0001");
    /// assert_eq!(&bf1 & &bf2, BitField::from_bin_str("0001 0000 0000 0111 1000 0101 0001"));
    ///```
    fn bitand(self, rhs: &BitField) -> BitField {
        let min_len = std::cmp::min(self.len(), rhs.len());
        let end = if min_len.bit() != 0 {min_len.byte() + 1} else {min_len.byte()};
        let mut res = Vec::<u8>::with_capacity(end);
        for i in 0..end {
            res.push(self.v[i] & rhs.v[i]);
        }
        // No need to clear bits past the end of the length since the & operation should zero them out
        BitField {v: res, length: min_len}
    }
}

impl std::ops::BitOr for &BitField {
    type Output = BitField;

    /// Returns the bitwise `|` operation on the two inputs. If the two inputs have different lengths,
    /// then the returned value will have the length of the shortest input.
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf1 = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
    /// let bf2 = BitField::from_bin_str("0101 0000 1100 0111 1010 1111 0001");
    /// assert_eq!(&bf1 | &bf2, BitField::from_bin_str("0111 1010 1100 1111 1110 1111 0111"));
    ///```
    fn bitor(self, rhs: &BitField) -> BitField {
        let min_len = std::cmp::min(self.len(), rhs.len());
        let end = if min_len.bit() != 0 {min_len.byte() + 1} else {min_len.byte()};
        let mut res = Vec::<u8>::with_capacity(end);
        for i in 0..end {
            res.push(self.v[i] | rhs.v[i]);
        }
        if min_len.bit() != 0 {
            let last = (res[end - 1] >> min_len.cbit()) << min_len.cbit();
            res[end - 1] = last;
        }
        BitField {v: res, length: min_len}
    }
}

impl std::ops::BitXor for &BitField {
    type Output = BitField;

    /// Returns the bitwise `^` operation on the two inputs. If the two inputs have different lengths,
    /// then the returned value will have the length of the shortest input.
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf1 = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
    /// let bf2 = BitField::from_bin_str("0101 0000 1100 0111 1010 1111 0001");
    /// assert_eq!(&bf1 ^ &bf2, BitField::from_bin_str("0110 1010 1100 1000 0110 1010 0110"));
    ///```
    fn bitxor(self, rhs: &BitField) -> BitField {
        let min_len = std::cmp::min(self.len(), rhs.len());
        let end = if min_len.bit() != 0 {min_len.byte() + 1} else {min_len.byte()};
        let mut res = Vec::<u8>::with_capacity(end);
        for i in 0..end {
            res.push(self.v[i] ^ rhs.v[i]);
        }
        if min_len.bit() != 0 {
            let last = (res[end - 1] >> min_len.cbit()) << min_len.cbit();
            res[end - 1] = last;
        }
        BitField {v: res, length: min_len}
    }
}

impl std::ops::Not for &BitField {
    type Output = BitField;

    /// Returns the bitwise `!` operation on the input. 
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
    /// assert_eq!(!&bf, BitField::from_bin_str("1100 0101 1111 0000 0011 1010 1000"));
    ///```
    fn not(self) -> BitField {
        let end = if self.length.bit() != 0 {self.length.byte() + 1} else {self.length.byte()};
        let mut res = Vec::<u8>::with_capacity(end);
        for i in 0..end {
            res.push(!self.v[i]);
        }
        if self.length.bit() != 0 {
            let last = (res[end - 1] >> self.length.cbit()) << self.length.cbit();
            res[end - 1] = last;
        }
        BitField {v: res, length: self.len()}
    }
}

impl std::ops::Shl<usize> for BitField {
    type Output = Self;

    /// Returns a [`BitField`](crate::BitField) with the bits shifted left by `rhs` bits.
    /// Bits that are dropped off the left side are wrapped around to will the right side.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf = BitField::from_bin_str("1100 0000 1111 00");
    /// let bf = bf << 2;
    /// assert_eq!(bf, BitField::from_bin_str("0000 0011 1100 11"));
    /// let bf = bf << 4;
    /// assert_eq!(bf, BitField::from_bin_str("0011 1100 1100 00"));
    ///```
    fn shl(self, rhs: usize) -> Self::Output {
        if rhs == 0 {
            return self;
        }

        let crhs = 8 - rhs;
        let max_bit = self.max_index().bit();

        let mut res = Vec::<u8>::new();
        for i in 0..(self.max_index().byte() - 1) {
            res.push((self.v[i] << rhs) | (self.v[i + 1] >> crhs));
        }

        let i = self.max_index().byte() - 1;
        if rhs <= max_bit {
            res.push((self.v[i] << rhs) | (self.v[i + 1] >> crhs));
            if max_bit != 0 {
                res.push((self.v[i + 1] << rhs) | (((self.v[0] >> crhs) << crhs) >> (max_bit - rhs)));
            }
        } else if max_bit != 0 {
            res.push((self.v[i] << rhs) | (self.v[i + 1] >> crhs) | (self.v[0] >> (crhs + max_bit)));
            res.push((self.v[0] >> crhs) << (8 - max_bit));
        } else {
            res.push((self.v[i] << rhs) | (self.v[0] >> crhs));
        }
        
        BitField {v: res, length: self.len()}
    }

}

pub trait FromBitField {
    fn from_bf(bf: &BitField) -> Self;
}

impl FromBitField for u8 {

    fn from_bf(bf: &BitField) -> u8 {
        let b = bf.len().bit();
        if b == 0 {
            bf.v[0]
        } else {
            bf.v[0] >> (8 - b)
        }
    }
}

#[cfg(test)]
mod bit_field_tests {
    use super::*;

    #[test]
    fn zeros() {
        assert_eq!(BitField::zeros(&BitIndex::new(2, 4)), BitField::from_bin_str("0000 0000 0000 0000 0000"));
        assert_eq!(BitField::zeros(&BitIndex::new(3, 0)), BitField::from_bin_str("0000 0000 0000 0000 0000 0000"));
        assert_eq!(BitField::zeros(&BitIndex::new(0, 0)), BitField::from_bin_str(""));
    }

    #[test]
    fn ones() {
        assert_eq!(BitField::ones(&BitIndex::new(2, 4)), BitField::from_bin_str("1111 1111 1111 1111 1111"));
        assert_eq!(BitField::ones(&BitIndex::new(3, 0)), BitField::from_bin_str("1111 1111 1111 1111 1111 1111"));
        assert_eq!(BitField::ones(&BitIndex::new(0, 0)), BitField::from_bin_str(""));
    }

    #[test]
    fn indexing() {
        let bf = BitField::from_vec(vec![0x00, 0xFF, 0xAB, 0x0F]);
        assert_eq!(bf.max_index(), BitIndex::new(4, 0));
        assert_eq!(bf.bit_at(&BitIndex::new(0, 0)), 0);
        assert_eq!(bf.bit_at(&BitIndex::new(1, 0)), 1);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 0)), 1);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 1)), 0);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 2)), 1);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 3)), 0);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 4)), 1);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 5)), 0);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 6)), 1);
        assert_eq!(bf.bit_at(&BitIndex::new(2, 7)), 1);
    }

    #[test]
    fn equality() {
        assert_ne!(BitField::from_bin_str("0101 0111 0000 1111"), BitField::from_bin_str("0101 0111 0000 1110"));
        assert_ne!(BitField::from_bin_str("0101 0111 0000 1111 11"), BitField::from_bin_str("0101 0111 0000 1111 10"));
        assert_ne!(BitField::from_bin_str("0101 0111 0000 1111 1"), BitField::from_bin_str("0101 0111 0000 1111 10"));
        assert_ne!(BitField::from_bin_str("0101 0111 0000 1111 11"), BitField::from_bin_str("0101 0111 0000 1111 1"));
    }

    #[test]
    fn parse() {
        assert_eq!(BitField::from_bin_str("0101 0111 0000 1111"), BitField::from_vec(vec![0x57, 0x0F]));
        assert_eq!(BitField::from_bin_str("0101_0111_0000_1111_0011_1100"), BitField::from_vec(vec![0x57, 0x0F, 0x3C]));
        assert_eq!(BitField::from_bin_str("0101_0111_0000_1").len(), BitIndex::new(1, 5));

        assert_eq!(BitField::from_bin_str("0101_0111_0000_1111"), BitField::from_hex_str("57 0f"));
        assert_eq!(BitField::from_bin_str("0101 1010 0000 1111 1100 0011 0110"), BitField::from_hex_str("5a 0f C3 6"));
    }

    #[test]
    fn truncate() {
        let mut bf = BitField::from_bin_str("0101 1111 0000 1010 1100 0011");
        bf.truncate(&BitIndex::new(2, 2));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1010 11"));
        bf.truncate(&BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1010"));
        bf.truncate(&BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 10"));
        bf.truncate(&BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 10"));
        bf.truncate(&BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 10"));
        bf.truncate(&BitIndex::new(1, 2));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 00"));
        bf.truncate(&BitIndex::new(0, 2));
        assert_eq!(bf, BitField::from_bin_str("01"));
    }

    #[test]
    fn extend() {
        let mut bf = BitField::from_bin_str("");
        bf.extend(&BitField::from_bin_str("01"));
        assert_eq!(bf, BitField::from_bin_str("01"));
        bf.extend(&BitField::from_bin_str("01"));
        assert_eq!(bf, BitField::from_bin_str("0101"));
        bf.extend(&BitField::from_bin_str("1111 0000 1111 0000"));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1111 0000"));
        bf.extend(&BitField::from_bin_str("0101 0"));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1111 0000 0101 0"));
        bf.extend(&BitField::from_bin_str("0011 00"));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1111 0000 0101 0001 100"));
        bf.extend(&BitField::from_bin_str("111"));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1111 0000 0101 0001 1001 11"));
        bf.extend(&BitField::from_bin_str("0101 11"));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1111 0000 0101 0001 1001 1101 0111"));
    }

    #[test]
    fn repeat() {
        let mut bf = BitField::from_bin_str("01");
        bf.repeat(1);
        assert_eq!(bf, BitField::from_bin_str("01"));
        bf.repeat(2);
        assert_eq!(bf, BitField::from_bin_str("0101"));
        bf.repeat(3);
        assert_eq!(bf, BitField::from_bin_str("0101 0101 0101"));
        bf.repeat(2);
        assert_eq!(bf, BitField::from_bin_str("0101 0101 0101 0101 0101 0101"));
        let mut bf2 = BitField::from_bin_str("01");
        bf.repeat(1000);
        bf2.repeat(12000);
        assert_eq!(bf, bf2);
    }

    #[test]
    fn bitwise() {
        let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100 0011");
        let bf2 = BitField::from_bin_str("1010 1100 1100 1001 1010 0011");
        assert_eq!(&bf1 & &bf2, BitField::from_bin_str("0000 1100 0000 1000 1000 0011"));
        assert_eq!(&bf1 | &bf2, BitField::from_bin_str("1111 1111 1100 1011 1110 0011"));
        assert_eq!(&bf1 ^ &bf2, BitField::from_bin_str("1111 0011 1100 0011 0110 0000"));
        assert_eq!(!&bf1, BitField::from_bin_str("1010 0000 1111 0101 0011 1100"));
        let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100");
        let bf2 = BitField::from_bin_str("1010 1100 1100 1001 1010 0011");
        assert_eq!(&bf1 & &bf2, BitField::from_bin_str("0000 1100 0000 1000 1000"));
        assert_eq!(&bf1 | &bf2, BitField::from_bin_str("1111 1111 1100 1011 1110"));
        assert_eq!(&bf1 ^ &bf2, BitField::from_bin_str("1111 0011 1100 0011 0110"));
        assert_eq!(!&bf1, BitField::from_bin_str("1010 0000 1111 0101 0011"));
        let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100 0011");
        let bf2 = BitField::from_bin_str("1010 1100 1100 1001 1010");
        assert_eq!(&bf1 & &bf2, BitField::from_bin_str("0000 1100 0000 1000 1000"));
        assert_eq!(&bf1 | &bf2, BitField::from_bin_str("1111 1111 1100 1011 1110"));
        assert_eq!(&bf1 ^ &bf2, BitField::from_bin_str("1111 0011 1100 0011 0110"));
    }

    #[test]
    fn shifts() {
        let bf = BitField::from_vec(vec![0x00, 0x00, 0xAB, 0x0F]);
        assert_eq!(bf.clone() << 2, BitField::from_vec(vec![0x00, 0x02, 0xAC, 0x3C]));
        assert_eq!(bf.clone() << 4, BitField::from_vec(vec![0x00, 0x0A, 0xB0, 0xF0]));
        assert_eq!(bf.clone() << 6, (bf.clone() << 4) << 2);
        assert_eq!(bf.clone() << 0, bf.clone());
    }

    #[test]
    fn shifts2() {
        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011");
        assert_eq!(bf.clone() << 2, BitField::from_bin_str("1011 1100 0001 0100 1110"));
        assert_eq!(bf.clone() << 4, BitField::from_bin_str("1111 0000 0101 0011 1010"));
        assert_eq!(bf.clone() << 6, BitField::from_bin_str("1100 0001 0100 1110 1011"));

        let bf = BitField::from_bin_str("1010 1111 0000 0101 01");
        assert_eq!(bf.clone() << 1, BitField::from_bin_str("010 1111 0000 0101 011"));
        assert_eq!(bf.clone() << 3, BitField::from_bin_str("0 1111 0000 0101 01101"));
        assert_eq!(bf.clone() << 5, BitField::from_bin_str("111 0000 0101 011010 1"));

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011 11");
        assert_eq!(bf.clone() << 2, BitField::from_bin_str("1011 1100 0001 0100 1111 10"));
        assert_eq!(bf.clone() << 4, BitField::from_bin_str("1111 0000 0101 0011 1110 10"));
        assert_eq!(bf.clone() << 6, BitField::from_bin_str("1100 0001 0100 1111 1010 11"));

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011 110");
        assert_eq!(bf.clone() << 1 << 2 << 3 << 4 << 5 << 6 << 7, bf.clone() << 5);
        // println!("{:?}", bf.clone() << 6);
        // todo!();
    }

    #[test]
    fn slices() {
        let bf = BitField::from_vec(vec![0xAB, 0xC0, 0xAB, 0xFF, 0x02]);

        let bx1 = BitIndex::new(2, 4);
        let bx2 = BitIndex::new(3, 4);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_vec(vec![0xBF]));

        let bx1 = BitIndex::new(2, 0);
        let bx2 = BitIndex::new(3, 0);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_vec(vec![0xAB]));

        let bx1 = BitIndex::new(2, 0);
        let bx2 = BitIndex::new(3, 2);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_bin_str("1010 1011 11"));

        let bx1 = BitIndex::new(1, 6);
        let bx2 = BitIndex::new(2, 2);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_bin_str("0010"));

        let bx1 = BitIndex::new(2, 2);
        let bx2 = BitIndex::new(2, 6);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_bin_str("1010"));

        let bx1 = BitIndex::new(3, 4);
        let bx2 = BitIndex::new(5, 0);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_bin_str("1111 0000 0010"));
    }

    #[test]
    fn slices2() {
        let bf = BitField::from_bin_str("1100 0011 1010 01");

        let bx1 = BitIndex::new(0, 4);
        let bx2 = BitIndex::new(1, 4);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_bin_str("0011 1010"));

        let bx1 = BitIndex::new(1, 2);
        let bx2 = BitIndex::new(1, 6);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_bin_str("1001"));

        let bx1 = BitIndex::new(0, 0);
        let bx2 = BitIndex::new(1, 6);
        let s = bf.bit_slice(&bx1, &bx2);
        assert_eq!(s, BitField::from_bin_str("1100 0011 1010 01"));
    }

    #[test]
    fn extract_u8() {
        let bf = BitField::from_bin_str("0011 1000 1010 0101 1110");
        assert_eq!(bf.extract_u8(BitIndex::new(0, 0)), 0x38);
        assert_eq!(bf.extract_u8(BitIndex::new(0, 1)), 0x71);
        assert_eq!(bf.extract_u8(BitIndex::new(0, 2)), 0xe2);
        assert_eq!(bf.extract_u8(BitIndex::new(0, 3)), 0xc5);
        assert_eq!(bf.extract_u8(BitIndex::new(0, 4)), 0x8a);
        assert_eq!(bf.extract_u8(BitIndex::new(0, 5)), 0x14);
        assert_eq!(bf.extract_u8(BitIndex::new(0, 6)), 0x29);
        assert_eq!(bf.extract_u8(BitIndex::new(0, 7)), 0x52);
        assert_eq!(bf.extract_u8(BitIndex::new(1, 0)), 0xa5);
    }
}  