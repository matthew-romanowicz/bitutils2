use crate::bit_index::{BitIndex, BitIndexable};
/*
#[derive(Clone, Debug)]
enum BitFieldConversionErrorKind {
    TooLong,
    TooShort
}

#[derive(Clone, Debug)]
pub struct BitFieldConversionError {
    kind: BitFieldConversionErrorKind
}

impl BitFieldConversionError {
    fn new(kind: BitFieldConversionErrorKind) -> BitFieldConversionError {
        BitFieldConversionError {kind}
    }
}

impl std::fmt::Display for BitFieldConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            BitFieldConversionErrorKind::TooLong => write!(f, "Bitfield is too long for data type"),
            BitFieldConversionErrorKind::TooShort => write!(f, "Bitfield is too short for data type"),
        }
    }    
}
*/

pub enum IntFormat {
    Unsigned,
    SignMagnitude,
    OnesCompliment,
    TwosCompliment,
    BaseMinusTwo
}

/// Represents a method that can be used for padding a [`BitField`]
pub enum BitPad {
    /// Represents all-ones padding (i.e. 0xFF)
    Ones,
    /// Represents all-zeros padding (i.e. 0x00)
    Zeros
}

impl BitPad {
    /// Generates a [`BitField`] of the specified length using the padding method
    /// specified by `self`. 
    ///
    /// # Panics
    /// Panics if `length` is negative
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex, bx, BitPad};
    ///
    /// let bf = BitPad::Zeros.bit_field(bx!(2, 4));
    /// assert_eq!(bf, BitField::from_hex_str("00 00 0"));
    ///
    /// let bf = BitPad::Ones.bit_field(bx!(2, 4));
    /// assert_eq!(bf, BitField::from_hex_str("ff ff f"));
    ///```
    pub fn bit_field(&self, length: BitIndex) -> BitField {
        if length.is_negative() {
            panic!("Negative length supplied to BitPad::bit_field: {}", length);
        }
        match self {
            BitPad::Ones => BitField::ones(length),
            BitPad::Zeros => BitField::zeros(length)
        }
    }
}


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
/// let bf8 = BitField::zeros(BitIndex::new(5, 0));
///
/// 
///```
/// ### Bitwise AND, OR, XOR, and NOT
///
/// The common bitwise operations (AND, OR, XOR, NOT) are supported. If the two sides have the same
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
    /// Panics if `length` is negative
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
        if length.is_negative() {
            panic!("Negative length supplied to BitField::new: {}", length)
        }
        BitField {v, length}
    }

    /// Returns a [`BitField`](crate::BitField) structure with the contents of the vector `v`.
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
    ///
    /// # Panics:
    /// Panics if `length` is negative
    pub fn zeros(length: BitIndex) -> BitField {
        if length.is_negative() {
            panic!("Negative length supplied to BitField::zeros: {}", length)
        }
        let end = if length.is_byte_boundary() {length.byte()} else {length.byte() + 1};
        BitField {v: vec![0; end], length}
    }

    /// Creates and returns a [`BitField`](crate::BitField) of ones (0xFF) with the given length.
    ///
    /// # Panics:
    /// Panics if `length` is negative
    pub fn ones(length: BitIndex) -> BitField {
        if length.is_negative() {
            panic!("Negative length supplied to BitField::ones: {}", length)
        }
        let mut v = Vec::<u8>::new();
        if length.is_byte_boundary() {
            v.resize(length.byte(), 0xff);
        } else {
            v.resize(length.byte() + 1, 0xff);
            let last = (v[length.byte()] >> length.cbit()) << length.cbit();
            v[length.byte()] = last;
        }
        BitField {v, length}
    }

    /// Parses a [`BitField`](crate::BitField) from a `str` of ones and zeros. Underscores and
    /// spaces are allowed and are ignored. Panics if any other character is encountered
    ///
    /// # Panics:
    /// Panics if `s` contains any character other than `0`, `1`, `_`, or ` `.
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
            if length.is_byte_boundary() {
                v.push(byte);
                byte = 0;
            }
        }
        if length.bit() != 0 {
            v.push(byte);
        }
        BitField {v, length}
    }

    /// Parses a [`BitField`](crate::BitField) from a `str` of hex characters (`0-9`, `a-f`, or `A-F`). 
    /// Underscores and spaces are allowed and are ignored. Panics if any other character is encountered.
    ///
    /// # Panics:
    /// Panics if `s` contains any character other than `0-9`, `a-f`, `A-F`, `_`, or ` `.
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

    pub fn to_bin_str(&self) -> String {
        let mut s = "".to_string();
        for b in &self.v {
            s.push_str(&format!("{:>08b}", b))
        }
        return s[..(self.len().total_bits() as usize)].to_string()
    }

    /// Returns the length of `self` as a [`BitIndex`](crate::BitIndex).
    pub fn len(&self) -> BitIndex {
        self.length
    }

    /// Returns `true` if the length is zero and `false` otherwise
    pub fn is_empty(&self) -> bool {
        self.length.is_zero()
    }

    /// Deletes the contents of the [`BitField`](crate::BitField) and sets the length to 0.
    pub fn clear(&mut self) {
        self.v.clear();
        self.length = BitIndex::new(0, 0);
    }

    /// Truncates the [`BitField`](crate::BitField) to `new_length` if `new_length` is shorter than 
    /// the current length. Does nothing otherwise.
    ///
    /// Panics if `new_length` is negative.
    pub fn truncate(&mut self, new_length: BitIndex) {
        if new_length.is_negative() {
            panic!("Negative length supplied to BitField::truncate: {}", new_length)
        }
        if self.length <= new_length {
            return
        }
        if new_length.is_byte_boundary() {
            self.v.truncate(new_length.byte());
        } else {
            self.v.truncate(new_length.byte() + 1);
            let last = (self.v[new_length.byte()] >> new_length.cbit()) << new_length.cbit();
            self.v[new_length.byte()] = last;
        }
        self.length = new_length;
    }

    /// Concatenates the argument onto the end of the [`BitField`](crate::BitField), adjusting the 
    /// length of the [`BitField`](crate::BitField) accordingly.
    pub fn extend(&mut self, other: &BitField) {
        if other.is_empty() {
            // Do nothing
        } else if self.length.is_byte_boundary() {
            self.v.extend(other.v.clone());
        } else {
            let cbit = self.length.cbit();
            self.v[self.length.byte()] |= other.v[0] >> self.length.bit();
            let mut carry = other.v[0] << cbit;
            let end = if other.length.is_byte_boundary() {other.length.byte()} else {other.length.byte() + 1};
            for i in 1..end {
                self.v.push((other.v[i] >> self.length.bit()) | carry);
                carry = other.v[i] << cbit;
            }
            if (self.length.bit() + other.length.bit() > 8) || other.length.is_byte_boundary() {
                self.v.push(carry);
            }
        
        }
        self.length += other.length;
    }

    /// Repeats a [`BitField`](crate::BitField) `n` times. If `n` is zero, the bitfield is cleared and if `n` is one, the bitfield
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

    /// Extends `self` to the new provided length by repeating as many times as needed to fill the new length. Final repetition is
    /// truncated to the specified length. If the specified length is less than `self`'s current length, then `self` is truncated
    /// to the new length.
    ///
    /// # Panics
    /// Panics if the provided length is negative or if `self` is empty.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 11");
    /// bf.repeat_until(BitIndex::new(5, 4));
    /// assert_eq!(bf, BitField::from_bin_str("0101 1100 1101 0111 0011 0101 1100 1101 0111 0011 0101"));
    ///
    /// // If the new length is less than the current length, then self is truncated.
    /// bf.repeat_until(BitIndex::new(0, 6));
    /// assert_eq!(bf, BitField::from_bin_str("0101 11"));
    ///```
    pub fn repeat_until(&mut self, new_length: BitIndex) {
        if new_length.is_negative() {
            panic!("Negative length supplied to BitField::repeat_until: {}", new_length);
        }
        if self.is_empty() {
            panic!("BitField::repeat_until called on empty BitField")
        }
        let n = new_length / &self.length;
        
        self.repeat(n as usize + 1);
        self.truncate(new_length);
        
    }

    /// Finds the index of the first `1` bit in `self`. Returns None if
    /// there are no zeros in `self` or if `self` is empty.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf = BitField::from_bin_str("0000 0101 1100 1100 0000");
    /// assert_eq!(bf.find_first_one().unwrap(), BitIndex::bits(5));
    /// let bf = BitField::from_bin_str("1000 0101 1100 1100 0000");
    /// assert_eq!(bf.find_first_one().unwrap(), BitIndex::bits(0));
    /// let bf = BitField::from_bin_str("0000 0000 0000 0000 0000 0000");
    /// assert!(bf.find_first_one().is_none());
    /// let bf = BitField::from_vec(vec![]);
    /// assert!(bf.find_first_one().is_none());
    ///```
    pub fn find_first_one(&self) -> Option<BitIndex> {
        self.v.iter().enumerate().find_map(|(i, b)| {
            if *b == 0 {
                None
            } else {
                let mut b = *b;
                let mut bit = 8;
                while b > 0 {
                    b >>= 1;
                    bit -= 1;
                }
                Some(BitIndex::new(i, bit))
            }
        })
    }

    /// Finds the index of the next `1` bit in `self`, starting from and including the
    /// provided start index. Returns None if there are no zeros in `self` 
    /// after or including `start` or if `self` is empty.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 1100 0000 0000 0010 0001 0000 0000");
    /// assert_eq!(bf.find_next_one(BitIndex::zero()).unwrap(), BitIndex::bits(1));
    /// assert_eq!(bf.find_next_one(BitIndex::bits(1)).unwrap(), BitIndex::bits(1));
    /// assert_eq!(bf.find_next_one(BitIndex::bits(11)).unwrap(), BitIndex::bits(22));
    /// assert!(bf.find_next_one(BitIndex::bits(29)).is_none());
    /// assert!(bf.find_next_one(BitIndex::bits(100)).is_none());
    ///```
    pub fn find_next_one(&self, start: BitIndex) -> Option<BitIndex> {
        self.v.iter().enumerate().skip(start.byte()).find_map(|(i, b)| {
            if *b == 0 {
                None
            } else {
                let mut b = *b;
                let mut bit = 8;
                if i == start.byte() {
                    b <<= start.bit();
                    if b == 0 {
                        return None
                    }
                    b >>= start.bit()
                }
                while b > 0 {
                    b >>= 1;
                    bit -= 1;
                }
                Some(BitIndex::new(i, bit))
            }
        })
    }

    /// Inserts the bits specified in `new` to the right of `self`, shifting the
    /// existing contents of `self` left to accommodate the new data without changing
    /// `self`'s length. If `new` is longer than `self`, then `self` will be overwritten
    /// with the rightmost data in `new`.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 1100 0011 1010");
    ///
    /// // When new is shorter than self, self's data is left shifted by new's length
    /// bf.shove_left(&BitField::from_bin_str("1101 00"));
    /// assert_eq!(bf, BitField::from_bin_str("0011 0000 1110 1011 0100"));
    ///
    /// // When new is the same length as self, self is overwritten with the data in new
    /// bf.shove_left(&BitField::from_bin_str("0101 1010 1101 0011 1100"));
    /// assert_eq!(bf, BitField::from_bin_str("0101 1010 1101 0011 1100"));
    ///
    /// // When new is longer than self, self is overwritten with the rightmost data in new
    /// bf.shove_left(&BitField::from_bin_str("1100 0011 1001 0110 0101 1100"));
    /// assert_eq!(bf, BitField::from_bin_str("0011 1001 0110 0101 1100"));
    ///```
    pub fn shove_left(&mut self, new: &BitField) {
        if new.len() < self.len() {
            *self <<= new.len().total_bits() as usize;
            self.truncate(self.len() - new.len());
            self.extend(new);
        } else if new.len() > self.len() {
            *self = new.bit_slice(&(new.len() - self.len()), &new.len());
        } else {
            *self = new.clone();
        }
    }

    /// Inserts the bits specified in `new` to the left of `self`, shifting the
    /// existing contents of `self` right to accommodate the new data without changing
    /// `self`'s length. If `new` is longer than `self`, then `self` will be overwritten
    /// with the leftmost data in `new`.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 1100 0011 1010");
    ///
    /// // When new is shorter than self, self's data is right shifted by new's length
    /// bf.shove_right(BitField::from_bin_str("1101 00"));
    /// assert_eq!(bf, BitField::from_bin_str("1101 0001 0111 0011 0000"));
    ///
    /// // When new is the same length as self, self is overwritten with the data in new
    /// bf.shove_right(BitField::from_bin_str("0101 1010 1101 0011 1100"));
    /// assert_eq!(bf, BitField::from_bin_str("0101 1010 1101 0011 1100"));
    ///
    /// // When new is longer than self, self is overwritten with the leftmost data in new
    /// bf.shove_right(BitField::from_bin_str("1100 0011 1001 0110 0101 1100"));
    /// assert_eq!(bf, BitField::from_bin_str("1100 0011 1001 0110 0101"));
    ///```
    pub fn shove_right(&mut self, mut new: BitField) {
        if new.len() < self.len() {
            self.truncate(self.len() - new.len());
            std::mem::swap(self, &mut new);
            self.extend(&new);
        } else if new.len() > self.len() {
            new.truncate(self.len());
            std::mem::swap(self, &mut new);
        } else {
            *self = new;
        }
    }

    /// Returns a slice of `self` that may extend beyond the length of `self`. The returned
    /// slice will be padded according to the provided `pad` parameter. If both `start` and
    /// `end` are less than `self`'s length, this is equivalant to 
    /// [`bit_slice`](crate::BitField::bit_slice). If both `start` and `end` are greater than
    /// `self`'s length, then the return value is entirely comprised of padding.
    ///
    /// #Panics
    /// Panics if `end` is less than `start` or if either is negative.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex, BitPad};
    ///
    /// let bf = BitField::from_bin_str("0101 1100 1100 0011 1010");
    ///
    /// // When the slice is contained within the bitfield, no padding is done.
    /// let slice_zeros = bf.slice_with_rpad(&BitIndex::new(0, 4), &BitIndex::new(2, 2), BitPad::Zeros);
    /// let slice_ones  = bf.slice_with_rpad(&BitIndex::new(0, 4), &BitIndex::new(2, 2), BitPad::Ones);
    /// assert_eq!(slice_zeros, BitField::from_bin_str("1100 1100 0011 10"));
    /// assert_eq!(slice_ones , BitField::from_bin_str("1100 1100 0011 10"));
    ///
    /// // When the slice is partially contained within the bitfield, then the remaining
    /// // portion will be filled in with padding.
    /// let slice_zeros = bf.slice_with_rpad(&BitIndex::new(1, 2), &BitIndex::new(3, 4), BitPad::Zeros);
    /// let slice_ones  = bf.slice_with_rpad(&BitIndex::new(1, 2), &BitIndex::new(3, 4), BitPad::Ones);
    /// assert_eq!(slice_zeros, BitField::from_bin_str("0000 1110 1000 0000 00"));
    /// assert_eq!(slice_ones , BitField::from_bin_str("0000 1110 1011 1111 11"));
    ///
    /// // When the slice is fully beyond the bitfield, then the entire slice will be filled in with padding.
    /// let slice_zeros = bf.slice_with_rpad(&BitIndex::new(2, 4), &BitIndex::new(3, 6), BitPad::Zeros);
    /// let slice_ones  = bf.slice_with_rpad(&BitIndex::new(2, 4), &BitIndex::new(3, 6), BitPad::Ones);
    /// assert_eq!(slice_zeros, BitField::from_bin_str("0000 0000 00"));
    /// assert_eq!(slice_ones , BitField::from_bin_str("1111 1111 11"));
    ///```
    pub fn slice_with_rpad(&self, start: &BitIndex, end: &BitIndex, pad: BitPad) -> BitField {
        if *end > self.len() {
            if *start >= self.len() {
                pad.bit_field(end - start)
            } else {
                let mut slice = self.bit_slice(start, &self.len());
                slice.extend(&pad.bit_field(end - &self.len()));
                slice
            }
        } else {
            self.bit_slice(start, end)
        }
    }

    /// Returns a slice of `self` that may extend beyond the contents of `self` in the positive and/or
    /// negative directions. The returned slice will be padded to the left (in the case of a negative
    /// `start` index) according to the `lpad` parameter, and to the right (in the case of a `end` index
    /// that is greater than `self`'s length) according to the provided `rpad` parameter. If neither `start`
    /// nor `end` are negative, then this is equivalent in function to [`slice_with_rpad`](crate::BitField::slice_with_rpad)
    ///
    /// # Panics
    /// Panics if `end` is less than `start`.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex, BitPad};
    ///
    /// let bf = BitField::from_bin_str("0101 1100 1100 0011 1010");
    ///
    /// // When the slice is contained within the bitfield, no padding is done.
    /// let slice_l0_r1 = bf.slice_with_pad(&BitIndex::new(0, 4), &BitIndex::new(2, 2), BitPad::Zeros, BitPad::Ones);
    /// let slice_r0_l1 = bf.slice_with_pad(&BitIndex::new(0, 4), &BitIndex::new(2, 2), BitPad::Ones, BitPad::Zeros);
    /// assert_eq!(slice_l0_r1, BitField::from_bin_str("1100 1100 0011 10"));
    /// assert_eq!(slice_r0_l1, BitField::from_bin_str("1100 1100 0011 10"));
    ///
    /// // When the slice is partially contained within the bitfield, then the remaining
    /// // portion will be filled in with padding.
    /// let slice_l0_r1 = bf.slice_with_pad(&BitIndex::new(1, 2), &BitIndex::new(3, 4), BitPad::Zeros, BitPad::Ones);
    /// let slice_r0_l1 = bf.slice_with_pad(&BitIndex::new(1, 2), &BitIndex::new(3, 4), BitPad::Ones, BitPad::Zeros);
    ///
    /// assert_eq!(slice_l0_r1, BitField::from_bin_str("0000 1110 10 11 1111 11"));
    /// assert_eq!(slice_r0_l1, BitField::from_bin_str("0000 1110 10 00 0000 00"));
    /// //                                              \----------/ \--------/
    /// //                                                 from bf    from rpad
    ///
    /// // When the slice starts at a negative index, then that portion will be filled in with padding.
    /// let slice_l0_r1 = bf.slice_with_pad(&-BitIndex::new(1, 2), &BitIndex::new(3, 4), BitPad::Zeros, BitPad::Ones);
    /// let slice_r0_l1 = bf.slice_with_pad(&-BitIndex::new(1, 2), &BitIndex::new(3, 4), BitPad::Ones, BitPad::Zeros);
    ///
    /// assert_eq!(slice_l0_r1, BitField::from_bin_str("00 0000 0000 0101 1100 1100 0011 1010 1111 1111"));
    /// assert_eq!(slice_r0_l1, BitField::from_bin_str("11 1111 1111 0101 1100 1100 0011 1010 0000 0000"));
    /// //                                              \----------/ \----------------------/ \--------/
    /// //                                                from lpad          from bf           from rpad
    ///
    /// // When the slice is fully negative, then it will be filled in completely with rpad
    /// let slice_l0_r1 = bf.slice_with_pad(&-BitIndex::new(1, 2), &-BitIndex::new(0, 2), BitPad::Zeros, BitPad::Ones);
    /// let slice_r0_l1 = bf.slice_with_pad(&-BitIndex::new(1, 2), &-BitIndex::new(0, 2), BitPad::Ones, BitPad::Zeros);
    ///
    /// assert_eq!(slice_l0_r1, BitField::from_bin_str("0000 0000"));
    /// assert_eq!(slice_r0_l1, BitField::from_bin_str("1111 1111"));
    /// //                                              \-------/
    /// //                                              from lpad
    ///```
    pub fn slice_with_pad(&self, start: &BitIndex, end: &BitIndex, lpad: BitPad, rpad: BitPad) -> BitField {
        if start.is_negative() {
            if end.is_negative() {
                lpad.bit_field(end - start)
            } else {
                let mut slice = lpad.bit_field(start.abs());
                slice.extend(&self.slice_with_rpad(&BitIndex::zero(), end, rpad));
                slice
            }
            
        } else {
            self.slice_with_rpad(start, end, rpad)
        }
    }

    /// Calculates the CRC of `self` using the provided initial value and 
    /// polynomial assuming big-endian bit order. Note that the polynomial paramter
    /// must not include the leading 1. 
    ///
    /// Panics if the `initial` and `polynomial` parameters are different lengths.
    pub fn crc_be(&self, initial: BitField, polynomial: BitField) -> BitField {
        let n = polynomial.len();
        if initial.len() != n {
            panic!("Length of 'initial' must be equal to length of 'polynomial'")
        }
        let mut current = BitIndex::zero();
        let mut slice = self.slice_with_rpad(&BitIndex::zero(), &n, BitPad::Zeros);

        slice ^= &initial;

        // let mut next = None;
        loop {
            loop {

                // Look for the next non-zero bit
                match slice.find_first_one() {
                    None => {
                        let slice_end = current + n;
                        if slice_end > self.len() {

                            slice.shove_left(&BitField::zeros(slice_end - self.len()));
                            return slice
                        } else {
                            current = slice_end;
                        }
                        break;
                    },
                    Some(offset) => {
                        let offset = offset + 1;
                        if current + offset > self.len() {
                            slice.shove_left(&BitField::zeros(self.len() - current));
                            return slice
                        }
                        let slice_end = current + n;

                        slice.shove_left(&self.slice_with_rpad(&slice_end, &(slice_end + offset), BitPad::Zeros));
                        
                        slice ^= &polynomial;
                        current += offset;
                    }
                }
            }

            // Find the next non-zero bit if one exists
            match self.find_next_one(current) {
                None => {
                    let slice_end = current + n;
                    if slice_end > self.len() {
                        slice.shove_left(&BitField::zeros(slice_end - self.len()));
                        return slice
                    } else {
                        return BitField::zeros(n)
                    }
                },
                Some(next) => {
                    current = next + 1;
                    let slice_end = current + n;
                    slice = self.slice_with_rpad(&current, &slice_end, BitPad::Zeros);
                    slice ^= &polynomial;
                }
            }
        }
    }

    /// Swaps the byte order of `self` from litte-endian to big-endian. Does nothing
    /// if `self` is less than or equal to one byte long. Note that in the case of 
    /// a [`BitField`](crate::BitField) that does not end on a byte coundary, this 
    /// method is not equivalent to [`swap_be_to_le`](crate::BitField::swap_be_to_le).
    /// This method will always undo the effect of [`swap_be_to_le`](crate::BitField::swap_be_to_le)
    /// and vice-versa.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 0110 1001 011");
    /// bf.swap_le_to_be();
    /// assert_eq!(bf, BitField::from_bin_str("0110 1101 0010 1011 100"));
    ///```
    pub fn swap_le_to_be(&mut self) {
        if self.length.ceil().byte() <= 1 {
            return
        }
        self.v.reverse();
        if !self.length.is_byte_boundary() {
            self.v[0] >>= self.length.cbit();
            for i in 0..self.v.len() {
                self.v[i] <<= self.length.cbit();
                if i + 1 < self.v.len() {
                    self.v[i] |= self.v[i + 1] >> self.length.bit();
                }
            }
        }
    }

    /// Swaps the byte order of `self` from big-endian to little-endian. Does nothing
    /// if `self` is less than or equal to one byte long. Note that in the case of 
    /// a [`BitField`](crate::BitField) that does not end on a byte coundary, this 
    /// method is not equivalent to [`swap_le_to_be`](crate::BitField::swap_le_to_be).
    /// This method will always undo the effect of [`swap_le_to_be`](crate::BitField::swap_le_to_be)
    /// and vice-versa.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 0110 1001 011");
    /// 
    /// bf.swap_be_to_le();    //             "0101 1100 0110 1001 011"
    /// assert_eq!(bf, BitField::from_bin_str("0100 1011 1110 0011 010"));
    ///```
    pub fn swap_be_to_le(&mut self) {
        if self.length.ceil().byte() <= 1 {
            return
        }
        self.v.reverse();
        if !self.length.is_byte_boundary() {
            for i in 0..self.v.len() {
                self.v[i] >>= self.length.cbit();
                if i + 1 < self.v.len() {
                    self.v[i] |= self.v[i + 1] << self.length.bit();
                } else {
                    self.v[i] <<= self.length.cbit();
                }
            }
        }
    }

    /// Maps a [`BitIndex`](crate::BitIndex) that corresponds to a big-endian location
    /// in `self` to one that corresponds to the same bit if self were little-endian.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex, BitIndexable};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 0110 1001 011");
    /// let mut bf2 = bf.clone();
    /// 
    /// bf2.swap_be_to_le();
    /// for i in 0..19 {
    ///     let bi1 = BitIndex::bits(i);
    ///     let bi2 = bf.map_be_to_le(&bi1);
    ///     println!("New Index: {:?}", bi2);
    ///    assert_eq!(bf.bit_at(&bi1), bf2.bit_at(&bi2));
    /// }
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 0110 1001 0110 1001");
    /// let mut bf2 = bf.clone();
    /// 
    /// bf2.swap_be_to_le();
    /// for i in 0..24 {
    ///     let bi1 = BitIndex::bits(i);
    ///     let bi2 = bf.map_be_to_le(&bi1);
    ///     println!("New Index: {:?}", bi2);
    ///    assert_eq!(bf.bit_at(&bi1), bf2.bit_at(&bi2));
    /// }
    ///```
    pub fn map_be_to_le(&self, index: &BitIndex) -> BitIndex {
        println!("Length: {:?}, index: {:?}", self.length, index);
        let b = self.length.ceil().byte() - index.byte();
        println!("b: {}", b);
        if self.length.is_byte_boundary() {
            // If the length is an even number of bytes, just return the same bit
            // in whatever byte corresponds to the given index after converting
            // endianness.
            BitIndex::new(b - 1, index.bit())
        } else {
            if index.bit() < self.length.bit() {
                if b == self.length.ceil().byte() {
                    BitIndex::new(b - 1, index.bit())
                } else {
                    let bit = index.bit() + self.length.cbit();
                    BitIndex::new(b + (bit >> 3) as usize - 1, bit & 0x07)
                }
                
            } else {
                BitIndex::new(b - 2, index.bit() - self.length.bit())
            }
        }
    }

    pub fn extract_u8(&self, start: BitIndex) -> u8 {
        if start.is_byte_boundary() {
            self.v[start.byte()]
        } else {
            (self.v[start.byte()] << start.bit()) | (self.v[start.byte() + 1] >> start.cbit())
        }
    }

    pub fn extract_u8_cyclical(&self, start: BitIndex) -> u8 {
        if self.length.byte() == 0 {
            // TODO: This is a stupid implementation
            let mut r = self.clone();
            r.repeat(8);
            return r.extract_u8_cyclical(start)
        }
        let start = start.rem_euclid(&self.length);
        let i = start.byte();
        if start.is_byte_boundary() {
            if i == self.length.byte() {
                // If the 8-bit span starts on the partial byte at the end of the field, we need
                // to grab some bits from the start.
                self.v[start.byte()] | self.v[0] >> self.length.bit()
            } else {
                self.v[start.byte()]
            }
        } else {
            let res = self.v[start.byte()] << start.bit();
            let last_byte = if self.length.is_byte_boundary() {
                self.length.byte() - 1
            } else {
                self.length.byte()
            };
            if i == last_byte {
                // 0101 0011 1010 0011 010
                // ---- --              ^- 
                if self.length.is_byte_boundary() {
                    res | (self.v[0] >> (8 - start.bit()))
                } else {
                    res | (self.v[0] >> (self.length.bit() - start.bit()))
                }
                
            } else {
                let next_byte = self.v[start.byte() + 1] >> start.cbit();
                if start + BitIndex::new(1, 0) > self.length {
                    //let diff = start + BitIndex::new(1, 0) - self.length;
                    let shift = start.cbit() + self.length.bit();
                    let first_byte = self.v[0] >> shift;//diff.cbit();
                    res | next_byte | first_byte
                } else {
                    res | next_byte
                }
            }
        }
    }

    /// Converts `self` into a boxed slice, where each element represents a byte. Returns `Err`
    /// if `self` does not end on a byte boundary and `Ok` otherwise. This function is helpful 
    /// in converting from a [`BitField`] to other variable-length types such as [`str`](std::str) 
    /// or [`Vec`](std::vec::Vec).
    /// 
    /// # Example:
    ///```rust
    /// use bitutils2::{BitField, BitIndex, BitIndexable};
    ///
    /// // If self ends on a byte boundary, then into_boxed_slice is a useful way
    /// // to convert to other variable-length types such as str.
    /// let bf = BitField::from_hex_str("48 65 6C 6C 6F 20 57 6F 72 6C 64 21");
    /// let boxed_slice = bf.into_boxed_slice().unwrap();
    /// let s = std::str::from_utf8(&boxed_slice).unwrap();
    /// assert_eq!(s, "Hello World!");
    ///
    /// // If self does not end on a byte boundary, into_boxed_slice returns Err.
    /// let bf = BitField::from_bin_str("0101 1100 1111");
    /// assert!(bf.into_boxed_slice().is_err());
    /// 
    ///```
    pub fn into_boxed_slice(self) -> Result<Box<[u8]>, ()> {
        if self.length.is_byte_boundary() {
            Ok(self.v.into_boxed_slice())
        } else {
            Err(())
        }
    }

    /// Converts `self` into a byte array. Returns `Err` if `self` does not end on a byte boundary 
    /// or is the wrong length for the destination type and `Ok` otherwise. This function is helpful 
    /// in converting from a [`BitField`] to fixed-length types such as integers or floats.
    /// 
    /// # Example:
    ///```rust
    /// use bitutils2::{BitField, BitIndex, BitIndexable};
    ///
    /// // If self ends on a byte boundary, then into_array is a useful way
    /// // to convert to fixed-length types such as u16.
    /// let bf = BitField::from_hex_str("AB CD");
    /// let arr = bf.into_array().unwrap();
    /// let n = u16::from_be_bytes(arr);
    /// assert_eq!(n, 0xABCD);
    ///
    /// // If self does not end on a byte boundary, into_array returns Err.
    /// let bf = BitField::from_bin_str("0101 1100 1111");
    /// assert!(bf.into_array::<2>().is_err());
    /// 
    /// // If self is the wrong length for the destination type, into_array returns Err.
    /// let bf = BitField::from_bin_str("0101 1100 1111 0000");
    /// assert!(bf.into_array::<4>().is_err());
    /// 
    ///```
    pub fn into_array<const N: usize>(self) -> Result<[u8; N], ()> {
        let boxed_slice = self.into_boxed_slice()?;
        match <Box<[u8]> as TryInto<Box<[u8; N]>>>::try_into(boxed_slice) {
            Ok(a) => Ok(*a),
            Err(_) => Err(())
        }
    }

    /// Returns the specified slice of `self` assuming that `self` is in a big-endian
    /// format. The bits in the slice are arranged in such a way that their relative
    /// magnitude is preserved when interpreted as a big-endian byte array. Equivalent
    /// to the [`bit_slice`](crate::BitIndexable::bit_slice) implementation for this type.
    pub fn slice_be(&self, start: &BitIndex, end: &BitIndex) -> BitField {
        self.bit_slice(start, end)
    }

    /// Returns the specified slice of `self` assuming that `self` is in a little-endian
    /// format and that the slice is contiguous. The bits in the slice are arranged in such
    /// a way that their relative magnitude is preserved when interpreted as a little-endian
    /// byte array.
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    /// //                                        0B5b                 2B7b
    /// //                                         v                     v
    /// let mut bf = BitField::from_bin_str("0101 1100 1010 0110 0101 1001 1111 0000");
    /// //                                  |____ _AAA|CCCB BBBB|EEDD DDD_|
    /// //                                  |MSB-->LSB|MSB-->LSB|MSB-->LSB|
    /// //                                     Byte 2    Byte 1    Byte 0
    /// //
    /// // AAA   = Least significant bits of least significant byte in slice
    /// // BBBBB = Least significant bits of second-to-least significant byte in slice
    /// // CCC   = Most significant bits of second-to-least significant byte in slice
    /// // DDDDD = Least significant bits of most significant byte in slice
    /// // EE    = Most signiciant bits of most significant byte in slice
    /// //                                     
    /// let bf2 = bf.slice_le(&BitIndex::new(0, 5), &BitIndex::new(2, 7));
    /// 
    /// //                                      BBBB BAAA|DDDD DCCC|EE
    /// assert_eq!(bf2, BitField::from_bin_str("0011 0100 0110 0101 01"));
    ///
    ///```
    pub fn slice_le(&self, start: &BitIndex, end: &BitIndex) -> BitField {
        // 0123 4567 89ab cdef ghij klmn opqr stuv
        //       --- ---- ---- ---- -
        // kcde fghi j567 89ab
        // j567 89ab kcde fghi
      
        // 0123 4567 89ab cdef ghij klmn opqr stuv
        //       --- ---- ---- ---- ---
        // bcde f567 ijkl m89a gh

        let length = end - start;
        let mut v = vec![0; length.ceil().byte()];

        for i in 0..(v.len() - 1) {
            let mut b = self.v[start.byte() + i];
            let mut c = self.v[start.byte() + i + 1];
            if i == 0 {
                // Move the portion of the byte within the slice to the MSB position
                b <<= start.bit(); 
            } else if start.byte() + i + 1 == end.byte() {
                // Move the portion of the byte within the slice to the LSB position
                c >>= end.cbit();
                //println!("{}, {}", i, c);
            } 
            v[i] = b >> start.bit();
            v[i] |= c << start.cbit();
        }

        v[length.ceil().byte() - 1] = ((self.v[end.byte()]  >> end.cbit()) >> start.bit()) << length.cbit();

        // // v[0] = ____ _567
        // v[0] = (self.v[start.byte()] << start.bit()) >> start.bit();
        // // v[0] |= bcde f___ = bcde f567
        // v[0] |= self.v[start.byte() + 1] << start.cbit();

        // // v[1] = ____ _89a
        // v[1] = self.v[start.byte() + 1] >> start.bit();
        // // v[1] |= ijkl m___
        // if start.byte() + 2 == end.byte() {
        //     v[1] |= (self.v[start.byte() + 2] >> end.cbit()) << start.cbit();
        // }
        
        // v[2] = ((self.v[start.byte() + 2] >> end.cbit()) >> start.bit()) << length.cbit();

        BitField::new(v, length)
    }

    /*
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("0101 1100 1010 0110 0101 1001 1111 0000");
    ///                                   // 0123 4567 89ab cdef ghij klmn opqr stuv
    /// let bf2 = bf.slice_le2(&BitIndex::new(1, 7), &BitIndex::new(3, 5));
    /// assert_eq!(bf2, BitField::from_bin_str("1100 1011 1101 00"));
    ///                                      // def0 1234 n89a bc
    ///
    /// let mut bf = BitField::from_bin_str("11011011000011110100100101000000");
    /// bf = bf.slice_le2(&BitIndex::bits(9), &BitIndex::bits(32));
    /// assert_eq!(bf, BitField::from_bin_str("11011011 00001111 1001001"));
    ///
    /// let test_f32 = std::f32::consts::PI;
    /// let full_bf = BitField::from_vec(test_f32.to_le_bytes().to_vec());
    /// let mut exp_bf = full_bf.slice_le2(&BitIndex::bits(1), &BitIndex::bits(9));
    /// let mut frac_bf = full_bf.slice_le2(&BitIndex::bits(9), &BitIndex::bits(32));
    /// frac_bf.pad_unsigned_le(BitIndex::bytes(4));
    /// let exp = u8::from_le_bytes(exp_bf.into_array().unwrap()) as i32;
    /// let frac = u32::from_le_bytes(frac_bf.into_array().unwrap());
    /// assert_eq!(exp, 128);
    /// assert_eq!(frac, 4788187);
    /// assert_eq!((2.0_f32).powi(exp - 127) * (1.0 + (frac as f32) * 2.0_f32.powi(-23)), std::f32::consts::PI);
    ///
    /// let test_f64 = std::f64::consts::PI;
    /// let full_bf = BitField::from_vec(test_f64.to_le_bytes().to_vec());
    /// let mut exp_bf = full_bf.slice_le2(&BitIndex::bits(1), &BitIndex::bits(12));
    /// let mut frac_bf = full_bf.slice_le2(&BitIndex::bits(12), &BitIndex::bits(64));
    /// exp_bf.pad_unsigned_le(BitIndex::bytes(2));
    /// frac_bf.pad_unsigned_le(BitIndex::bytes(8));
    /// let exp = u16::from_le_bytes(exp_bf.into_array().unwrap()) as i32;
    /// let frac = u64::from_le_bytes(frac_bf.into_array().unwrap());
    /// assert_eq!(exp, 1024);
    /// assert_eq!(frac, 2570638124657944);
    /// assert_eq!((2.0_f64).powi(exp - 1023) * (1.0 + (frac as f64) * 2.0_f64.powi(-52)), std::f64::consts::PI);
    ///
    ///```
    pub fn slice_le2(&self, start: &BitIndex, end: &BitIndex) -> BitField {
        // 0123 4567 89ab cdef ghij klmn opqr stuv
        //       --- ---- ---- ---- -
        // 0123 4567 89ab cdef ghij klmn opqr stuv
        // ---- -    ---- ----       ---
        // def0 1234 
      
        // 0123 4567 89ab cdef ghij klmn opqr stuv
        // ---- -    ---- ----         -
        // def0 1234 n89a bc

        // 0123 4567 89ab cdef ghij klmn opqr stuv
        // ---- ---- ---- ----  --- ----
        // def0 1234 n89a bc

        // 0123 4567 89ab cdef ghij klmn opqr stuv
        //                     ---^       ^-- ----
        // stuv ghij pqr

        if start.byte() == end.byte() {
            let b = self.length.ceil().byte() - 1 - (end.ceil().byte() - 1);
            let start = BitIndex::new(b, start.bit());
            let end = BitIndex::new(b, end.bit());
            return self.bit_slice(&start, &end)
        }

        println!("Test: {}", end.bit() + start.cbit());
        let length = BitIndex::bytes(end.byte() - start.byte() - 1) + BitIndex::bits((end.bit() + start.cbit()) as usize);
        let start_byte = self.length.ceil().byte() - 1 - start.byte();
        let start_bit = start.bit();
        println!("Original Start: {:?}", start);
        println!("Original End: {:?}", end);
        // println!("Converted Start: {:?}", self.map_be_to_le(&end));
        // println!("Converted End: {:?}", self.map_be_to_le(&start));
        let start2 = BitIndex::new(self.length.ceil().byte() - 1 - (end.ceil().byte() - 1), end.bit());
        let end2 = BitIndex::new(start_byte, start_bit);
        println!("Start2: {:?}", start2);
        println!("End2: {:?}", end2);
        let (start, end) = if *end == self.length {
            // End includes least significant bit
            if self.length.byte() == 0 {
                (self.length.clone(), self.map_be_to_le(&start))
            } else {
                (BitIndex::bytes(1), self.map_be_to_le(&start))
            }
        } else {
            (self.map_be_to_le(&end), self.map_be_to_le(&start))
        };
        // let (start, end) = (self.map_be_to_le(&end), self.map_be_to_le(&start));
        println!("Length: {:?}", length);
        println!("Start: {:?}", start);
        println!("End: {:?}", end);
        let mut v = vec![0; length.ceil().byte()];

        // if start.byte() + length.ceil().byte() -1 + 1 >= self.length.ceil().byte() - 1

        for i in 0..(v.len()) {
            let mut b = self.v[start.byte() + i];
            // let mut c = self.v[start.byte() + i + 1];
            // if i == 0 {
            //     // Move the portion of the byte within the slice to the LSB position
            //     // b >>= start.cbit(); 
            // } else if start.byte() + i + 1 == end.byte() {
            //     // Move the portion of the byte within the slice to the LSB position
            //     // c <<= end.cbit();
            //     // println!("{}, {}", i, c);
            // } 
            println!("b = {}", b);
            if start.is_byte_boundary() {
                v[i] = b;
            } else {
                println!("b >> {} = {}", start.cbit(), b >> start.cbit());
                v[i] = b >> start.cbit();
                // v[i] |= c << start.bit();
                if start.byte() + i + 1 < self.v.len() {
                    let c = self.v[start.byte() + i + 1];
                    println!("c = {}", c);
                    println!("v << {} = {}", start.bit(), c << start.bit());
                    v[i] |= c << start.bit();
                }
            }
            
        }
        let n_bytes = v.len();
        if length.bit() != 0 {
            v[n_bytes - 1] = 
            
            v[n_bytes - 1] << length.cbit();
        }
        

        // v[length.ceil().byte() - 1] = ((self.v[end.byte()]  >> end.cbit()) >> start.bit()) << length.cbit();

        // // v[0] = ____ _567
        // v[0] = (self.v[start.byte()] << start.bit()) >> start.bit();
        // // v[0] |= bcde f___ = bcde f567
        // v[0] |= self.v[start.byte() + 1] << start.cbit();

        // // v[1] = ____ _89a
        // v[1] = self.v[start.byte() + 1] >> start.bit();
        // // v[1] |= ijkl m___
        // if start.byte() + 2 == end.byte() {
        //     v[1] |= (self.v[start.byte() + 2] >> end.cbit()) << start.cbit();
        // }
        
        // v[2] = ((self.v[start.byte() + 2] >> end.cbit()) >> start.bit()) << length.cbit();

        BitField::new(v, length)
    }
    */

    /// Converts the data contained within `self` to a big-endian unsigned
    /// integer by removing the sign information according to the source
    /// format provided. Returns `true` if the sign was negative before being
    /// removed, even if the magnitude is `0`. Returns `false` if the sign was
    /// positive, even if the magnitude is `0`.
    ///
    /// If the source format is `Unsigned`, then `self` is not mutated and 
    /// `false` is returned.
    pub fn convert_unsigned_be(&mut self, src_format: IntFormat) -> bool {
        let mut negative: bool;

        match src_format {
            IntFormat::SignMagnitude => {
                negative = self.bit_at(&BitIndex::zero()) != 0;
                self.v[0] &= 0x7f;
            },
            IntFormat::OnesCompliment => {
                negative = self.bit_at(&BitIndex::zero()) != 0;
                if negative {
                    for b in self.v.iter_mut() {
                        *b ^= 0xff;
                    }
                    if !self.length.is_byte_boundary() {
                        let last_byte = self.v.len() - 1;
                        self.v[last_byte] &= 0xff << self.length.cbit();
                    }
                }
            },
            IntFormat::TwosCompliment => {
                negative = self.bit_at(&BitIndex::zero()) != 0;
                if negative {
                    let mut carry = true;
                    for b in self.v.iter_mut().rev() {
                        if carry {
                            (*b, carry) = b.overflowing_sub(1);
                        }
                        *b ^= 0xff;
                    }
                    if !self.length.is_byte_boundary() {
                        let last_byte = self.v.len() - 1;
                        self.v[last_byte] &= 0xff << self.length.cbit();
                    }
                } 
            },
            IntFormat::Unsigned => {
                negative = false
            },
            IntFormat::BaseMinusTwo => {
                // If the BitField ends with an odd number of bits, then
                // it needs to be accounted for since the bits are counted 
                // from the LSB, so which bits are even and odd will be switched 
                let odd_bits = self.length.bit() & 0x01 != 0;

                // Iterate through from the most significant to least
                // significant bytes to tell whether the highest value
                // bit is negative or positive. This will determine the
                // sign of the result. Also record the location of the
                // MSB so that we can save some iterations in the subtration
                negative = false;
                let mut num_significant_bytes = self.v.len();
                for (i, b) in self.v.iter().enumerate() {
                    if *b != 0 {
                        negative = ((*b & 0xaa) > (*b & 0x55)) ^ odd_bits;
                        num_significant_bytes -= i;
                        break;
                    }
                }

                // Subtract the even bits from the odd bits if positive,
                // and vice versa if negative to guarantee a positive result.
                let mut carry = false;
                let mut minuend;
                let mut subtrahend;
                for b in self.v.iter_mut().rev().take(num_significant_bytes) {
                    (minuend, subtrahend) = match negative ^ odd_bits {
                        true => (*b & 0xaa, *b & 0x55),
                        false => (*b & 0x55, *b & 0xaa)
                    };
                    if carry {
                        subtrahend += 1;
                    }
                    (*b, carry) = minuend.overflowing_sub(subtrahend);
                    
                }
            }
        };

        return negative
    }

    /// Converts the data contained within `self` to a little-endian unsigned
    /// integer by removing the sign information according to the source
    /// format provided. Returns `true` if the sign was negative before being
    /// removed, even if the magnitude is `0`. Returns `false` if the sign was
    /// positive, even if the magnitude is `0`.
    ///
    /// If the source format is `Unsigned`, then `self` is not mutated and 
    /// `false` is returned.
    pub fn convert_unsigned_le(&mut self, src_format: IntFormat) -> bool {
        let mut negative: bool;

        let msb = BitIndex::new(self.len().ceil().byte() - 1, 0);

        match src_format {
            IntFormat::SignMagnitude => {
                negative = self.bit_at(&msb) != 0;
                self.v[msb.byte()] &= 0x7f;
            },
            IntFormat::OnesCompliment => {
                negative = self.bit_at(&msb) != 0;
                if negative {
                    for b in self.v.iter_mut() {
                        *b ^= 0xff;
                    }
                    if !self.length.is_byte_boundary() {
                        let last_byte = self.v.len() - 1;
                        self.v[last_byte] &= 0xff << self.length.cbit();
                    }
                }
            },
            IntFormat::TwosCompliment => {
                negative = self.bit_at(&msb) != 0;
                if negative {
                    let mut carry = true;
                    for b in self.v.iter_mut() {
                        if carry {
                            (*b, carry) = b.overflowing_sub(1);
                        }
                        *b ^= 0xff;
                    }
                    if !self.length.is_byte_boundary() {
                        let last_byte = self.v.len() - 1;
                        self.v[last_byte] &= 0xff << self.length.cbit();
                    }
                } 
            },
            IntFormat::Unsigned => {
                negative = false
            },
            IntFormat::BaseMinusTwo => {
                // If the BitField ends with an odd number of bits, then
                // it needs to be accounted for since the bits are counted 
                // from the LSB, so which bits are even and odd will be switched 
                // in the leftmost byte
                let odd_bits = self.length.bit() & 0x01 != 0;

                let last_byte = self.v.len() - 1;

                // Iterate through from the most significant to least
                // significant bytes to tell whether the highest value
                // bit is negative or positive. This will determine the
                // sign of the result. Also record the location of the
                // MSB so that we can save some iterations in the subtration
                negative = false;
                let mut num_significant_bytes = self.v.len();
                for (i, b) in self.v.iter().rev().enumerate() {
                    if *b != 0 {
                        negative = ((*b & 0xaa) > (*b & 0x55)) ^ (odd_bits && i == last_byte);
                        num_significant_bytes -= i;
                        break;
                    }
                }

                // Subtract the even bits from the odd bits if positive,
                // and vice versa if negative to guarantee a positive result.
                let mut carry = false;
                let mut minuend;
                let mut subtrahend;
                for (i, b) in self.v.iter_mut().enumerate().take(num_significant_bytes) {
                    (minuend, subtrahend) = match negative ^ (odd_bits && i == last_byte) {
                        true => (*b & 0xaa, *b & 0x55),
                        false => (*b & 0x55, *b & 0xaa)
                    };
                    if carry {
                        subtrahend += 1;
                    }
                    (*b, carry) = minuend.overflowing_sub(subtrahend);
                    
                }
            }
        }

        return negative
    }

    /// Pads `self` to the specified length in such a way that when interpreted
    /// as an unsigned big-endian integer, the value is unchanged. More specifically,
    /// `self` is extended to the new length by padding the left side with zeros.
    ///
    /// This also works for base -2 numbers
    /// 
    /// Does nothing if the provided length is less than or equal to `self`'s current
    /// length.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_vec(vec![0x30, 0x39]);
    /// assert_eq!(u16::from_be_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_unsigned_be(BitIndex::bits(32));
    /// assert_eq!(u32::from_be_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_unsigned_be(BitIndex::bits(64));
    /// assert_eq!(u64::from_be_bytes(bf.clone().into_array().unwrap()), 12345);
    ///```
    pub fn pad_unsigned_be(&mut self, new_length: BitIndex) {
        if self.length < new_length {
            let delta = new_length - self.length;
            let pad = BitField::zeros(delta);
            let original = std::mem::replace(self, pad);
            self.extend(&original);
        }
    }

    /// Pads `self` to the specified length in such a way that when interpreted
    /// as an unsigned little-endian integer, the value is unchanged. More specifically,
    /// `self` is extended to the new length by padding the right side with zeros
    /// and, if `self` doesn't currently end on a byte boundary, shifting the contents
    /// of the last partial byte so that they retain the same significance
    /// 
    /// This also works for base -2 numbers
    ///
    /// Does nothing if the provided length is less than or equal to `self`'s current
    /// length.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_vec(vec![0x39, 0x30]);
    /// assert_eq!(u16::from_le_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_unsigned_le(BitIndex::bits(32));
    /// assert_eq!(u32::from_le_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_unsigned_le(BitIndex::bits(64));
    /// assert_eq!(u64::from_le_bytes(bf.clone().into_array().unwrap()), 12345);
    ///```
    pub fn pad_unsigned_le(&mut self, new_length: BitIndex) {
        if self.length < new_length {

            // Pad the left side with zeros to the new length
            let pad = BitField::zeros(new_length - self.length);
            let old_length = self.length.clone();
            self.extend(&pad);


            if !old_length.is_byte_boundary() {
                // If `self` ended in a partial byte, that data will need to be
                // shifted so that it retains the same significance.
                let shift: u8;
                if new_length.byte() > old_length.byte() {
                    // If a new byte was added, push the partial byte at the end 
                    // of the original to the LSB position
                    shift = old_length.cbit();
                } else {
                    // If a new byte hasn't been added, push the partial byte at
                    // the end to the new LSB position (not the end of the byte)
                    shift = new_length.bit() - old_length.bit();
                }
                self.v[old_length.byte()] = self.v[old_length.byte()] >> shift;
            }
        }
    }

    /// Pads `self` to the specified length in such a way that when interpreted
    /// as an signed twos-compliment big-endian integer, the value is unchanged. 
    /// More specifically, `self` is extended to the new length by padding the left 
    /// side with either zeros or ones depending on the value of the most significant
    /// bit. 
    ///
    /// This also works for one's compliment numbers.
    /// 
    /// Does nothing if the provided length is less than or equal to `self`'s current
    /// length.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_vec(vec![0x30, 0x39]);
    /// assert_eq!(i16::from_be_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_twos_compliment_be(BitIndex::bits(32));
    /// assert_eq!(i32::from_be_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_twos_compliment_be(BitIndex::bits(64));
    /// assert_eq!(i64::from_be_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// let mut bf = BitField::from_vec(vec![0xcf, 0xc7]);
    /// assert_eq!(i16::from_be_bytes(bf.clone().into_array().unwrap()), -12345);
    ///
    /// bf.pad_twos_compliment_be(BitIndex::bits(32));
    /// assert_eq!(i32::from_be_bytes(bf.clone().into_array().unwrap()), -12345);
    ///
    /// bf.pad_twos_compliment_be(BitIndex::bits(64));
    /// assert_eq!(i64::from_be_bytes(bf.clone().into_array().unwrap()), -12345);
    ///```
    pub fn pad_twos_compliment_be(&mut self, new_length: BitIndex) {
        if self.length < new_length {
            let delta = new_length - self.length;
            let pad = if self.bit_at(&BitIndex::zero()) == 0 {
                BitField::zeros(delta)
            } else {
                BitField::ones(delta)
            };
            let original = std::mem::replace(self, pad);
            self.extend(&original);
        }
    }

    /// Pads `self` to the specified length in such a way that when interpreted
    /// as an signed twos-compliment little-endian integer, the value is unchanged. 
    /// More specifically, `self` is extended to the new length by padding the right 
    /// side with either zeros or ones depending on the value of the most significant
    /// byte. In addition, if `self` doesn't currently end on a byte boundary, 
    /// shifting the contents of the last partial byte so that they retain the same 
    /// significance.
    ///
    /// This also works for one's compliment numbers.
    /// 
    /// Does nothing if the provided length is less than or equal to `self`'s current
    /// length.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_vec(vec![0x39, 0x30]);
    /// assert_eq!(i16::from_le_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_twos_compliment_le(BitIndex::bits(32));
    /// assert_eq!(i32::from_le_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// bf.pad_twos_compliment_le(BitIndex::bits(64));
    /// assert_eq!(i64::from_le_bytes(bf.clone().into_array().unwrap()), 12345);
    ///
    /// let mut bf = BitField::from_vec(vec![0xc7, 0xcf]);
    /// assert_eq!(i16::from_le_bytes(bf.clone().into_array().unwrap()), -12345);
    ///
    /// bf.pad_twos_compliment_le(BitIndex::bits(32));
    /// assert_eq!(i32::from_le_bytes(bf.clone().into_array().unwrap()), -12345);
    ///
    /// bf.pad_twos_compliment_le(BitIndex::bits(64));
    /// assert_eq!(i64::from_le_bytes(bf.clone().into_array().unwrap()), -12345);
    ///```
    pub fn pad_twos_compliment_le(&mut self, new_length: BitIndex) {
        if self.length < new_length {

            let sign_index = if self.length.is_byte_boundary() {
                BitIndex::new(self.length.byte() - 1, 0)
            } else {
                BitIndex::new(self.length.byte(), 0)
            };

            let negative = self.bit_at(&sign_index) != 0;

            let old_length = self.length.clone();


            // Determine how many bytes to add after the current byte (even if it's partial)
            let new_bytes = new_length.ceil().byte() - self.v.len();

            // If the number is negative, pad out the new bytes with 1
            if negative {
                self.v.extend(vec![0xff; new_bytes]);
                let last_byte = self.v.len() - 1;
                if !new_length.is_byte_boundary() {
                    // If the new length has a partial byte, zero out the extra bits
                    self.v[last_byte] &= 0xff << new_length.cbit();
                }
            } else {
                self.v.extend(vec![0x00; new_bytes]);
            }
            // Update the length to account for the new bytes added
            self.length = new_length;
            


            if !old_length.is_byte_boundary() {
                // If `self` ended in a partial byte, that data will need to be
                // shifted so that it retains the same significance.
                let shift: u8;
                if new_length.byte() > old_length.byte() {
                    // If a new byte was added, push the partial byte at the end 
                    // of the original to the LSB position
                    shift = old_length.cbit();
                } else {
                    // If a new byte hasn't been added, push the partial byte at
                    // the end to the new LSB position (not the end of the byte)
                    shift = new_length.bit() - old_length.bit();
                }

                // If the number is negative, shift the data in the last byte over
                // and fill in with ones. Otherwise, don't fill.
                if negative {
                    self.v[old_length.byte()] = 0xff << (8 - shift) | (self.v[old_length.byte()] >> shift);
                } else {
                    self.v[old_length.byte()] = self.v[old_length.byte()] >> shift;
                }
                
            }
        }
    }

    /// Pads `self` to the specified length in such a way that when interpreted
    /// as an sign-magnitude big-endian integer, the value is unchanged. More 
    /// specifically, the sign bit is removed, `self` is extended to the new 
    /// length by padding the left side with zeros, and the sign bit is reinserted
    /// at the new MSB location.
    /// 
    /// Does nothing if the provided length is less than or equal to `self`'s current
    /// length.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_vec(vec![0x30, 0x39]);
    /// let u = u16::from_be_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000) >> 15, 0); // Sign = positive
    ///
    /// bf.pad_sign_magnitude_be(BitIndex::bits(32));
    /// let u = u32::from_be_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x80000000) >> 31, 0); // Sign = positive
    ///
    /// bf.pad_sign_magnitude_be(BitIndex::bits(64));
    /// let u = u64::from_be_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffffffffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000000000000000) >> 63, 0); // Sign = positive
    ///
    /// let mut bf = BitField::from_vec(vec![0xb0, 0x39]);
    /// let u = u16::from_be_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000) >> 15, 1); // Sign = negative
    ///
    /// bf.pad_sign_magnitude_be(BitIndex::bits(32));
    /// let u = u32::from_be_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x80000000) >> 31, 1); // Sign = negative
    ///
    /// bf.pad_sign_magnitude_be(BitIndex::bits(64));
    /// let u = u64::from_be_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffffffffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000000000000000) >> 63, 1); // Sign = negative
    ///```
    pub fn pad_sign_magnitude_be(&mut self, new_length: BitIndex) {
        if self.length < new_length {
            let delta = new_length - self.length;

            // Read and remove sign bit at the MSB position
            let sign = self.v[0] & 0x80;
            self.v[0] &= 0x7f;

            // Left pad to the new length with zeros
            let pad = BitField::zeros(delta);
            let original = std::mem::replace(self, pad);
            self.extend(&original);

            // Insert the sign at the new MSB position
            self.v[0] |= sign;
        }
    }

    /// Pads `self` to the specified length in such a way that when interpreted
    /// as an sign-magnitude little-endian integer, the value is unchanged. More 
    /// specifically, the sign bit is removed, `self` is extended to the new 
    /// length using [`pad_unsigned_le`](BitField::pad_unsigned_le), and the sign 
    /// bit is reinserted at the new MSB location.
    /// 
    /// Does nothing if the provided length is less than or equal to `self`'s current
    /// length.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_vec(vec![0x39, 0x30]);
    /// let u = u16::from_le_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000) >> 15, 0); // Sign = positive
    ///
    /// bf.pad_sign_magnitude_le(BitIndex::bits(32));
    /// let u = u32::from_le_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x80000000) >> 31, 0); // Sign = positive
    ///
    /// bf.pad_sign_magnitude_le(BitIndex::bits(64));
    /// let u = u64::from_le_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffffffffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000000000000000) >> 63, 0); // Sign = positive
    ///
    /// let mut bf = BitField::from_vec(vec![0x39, 0xb0]);
    /// let u = u16::from_le_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000) >> 15, 1); // Sign = negative
    ///
    /// bf.pad_sign_magnitude_le(BitIndex::bits(32));
    /// let u = u32::from_le_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x80000000) >> 31, 1); // Sign = negative
    ///
    /// bf.pad_sign_magnitude_le(BitIndex::bits(64));
    /// let u = u64::from_le_bytes(bf.clone().into_array().unwrap());
    /// assert_eq!(u & 0x7fffffffffffffff, 12345); // Magnitude = 12345
    /// assert_eq!((u & 0x8000000000000000) >> 63, 1); // Sign = negative
    ///```
    pub fn pad_sign_magnitude_le(&mut self, new_length: BitIndex) {
        if self.length < new_length {

            // Read and remove sign bit at the MSB position
            let msb = self.length.ceil().byte() - 1;
            let sign = self.v[msb] & 0x80;
            self.v[msb] &= 0x7f;

            // Pad as an unsigned value (since it pretty much is now)
            self.pad_unsigned_le(new_length);

            // Insert the sign at the new MSB position
            let msb = self.length.ceil().byte() - 1;
            self.v[msb] |= sign;
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
                // println!("{} {}", i, carry);
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

impl Default for BitField {
    fn default() -> BitField {
        BitField::new(vec![], BitIndex::zero())
    }
}

impl std::cmp::PartialEq for BitField {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            false
        } else if self.len().is_byte_boundary() {
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
        // Figure out the number of bytes for the shortest input and generate a new vector with that
        // capacity
        let min_len = std::cmp::min(self.len(), rhs.len());
        let end = min_len.ceil().byte();
        let mut res = Vec::<u8>::with_capacity(end);

        // Perform the bitwise operation on all bytes
        for i in 0..end {
            res.push(self.v[i] & rhs.v[i]);
        }
        // No need to clear bits past the end of the length since the & operation should zero them out
        BitField {v: res, length: min_len}
    }
}

impl std::ops::BitAndAssign<&BitField> for BitField  {

    /// Transforms `self` to have the value of `self & rhs`. If the two inputs have different lengths,
    /// then the resulting value will have the length of the shortest input.
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf1 = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
    /// bf1 &= &BitField::from_bin_str("0101 0000 1100 0111 1010 1111 0001");
    /// assert_eq!(bf1, BitField::from_bin_str("0001 0000 0000 0111 1000 0101 0001"));
    ///```
    fn bitand_assign(&mut self, rhs: &BitField) {
        // Figure out the number of bytes for the shortest input and truncate `self` accordingly
        let min_len = std::cmp::min(self.len(), rhs.len());
        let end = min_len.ceil().byte();
        self.v.truncate(end);

        // Perform the bitwise operation on all bytes
        for i in 0..end {
            self.v[i] &= rhs.v[i];
        }
        // No need to clear bits past the end of the length since the & operation should zero them out

        // Update the length in case `self` was truncated
        self.length = min_len;
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
        let end = min_len.ceil().byte();
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

impl std::ops::BitOrAssign<&BitField> for BitField  {

    /// Transforms `self` to have the value of `self | rhs`. If the two inputs have different lengths,
    /// then the resulting value will have the length of the shortest input.
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf1 = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
    /// bf1 |= &BitField::from_bin_str("0101 0000 1100 0111 1010 1111 0001");
    /// assert_eq!(bf1, BitField::from_bin_str("0111 1010 1100 1111 1110 1111 0111"));
    ///```
    fn bitor_assign(&mut self, rhs: &BitField) {
        // Figure out the number of bytes for the shortest input and truncate `self` accordingly
        let min_len = std::cmp::min(self.len(), rhs.len());
        let end = min_len.ceil().byte();
        self.v.truncate(end);

        // Perform the bitwise operation on all bytes
        for i in 0..end {
            self.v[i] |= rhs.v[i];
        }

        // Ensure that the bits past the end of the bitfield are zeroed
        if min_len.bit() != 0 {
            let last = (self.v[end - 1] >> min_len.cbit()) << min_len.cbit();
            self.v[end - 1] = last;
        }

        // Update the length in case `self` was truncated
        self.length = min_len;
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
        let end = min_len.ceil().byte();
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

impl std::ops::BitXorAssign<&BitField> for BitField  {

    /// Transforms `self` to have the value of `self ^ rhs`. If the two inputs have different lengths,
    /// then the resulting value will have the length of the shortest input.
    ///
    /// # Example
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf1 = BitField::from_bin_str("0011 1010 0000 1111 1100 0101 0111");
    /// bf1 ^= &BitField::from_bin_str("0101 0000 1100 0111 1010 1111 0001");
    /// assert_eq!(bf1, BitField::from_bin_str("0110 1010 1100 1000 0110 1010 0110"));
    ///```
    fn bitxor_assign(&mut self, rhs: &BitField) {
        // Figure out the number of bytes for the shortest input and truncate `self` accordingly
        let min_len = std::cmp::min(self.len(), rhs.len());
        let end = min_len.ceil().byte();
        self.v.truncate(end);

        // Perform the bitwise operation on all bytes
        for i in 0..end {
            self.v[i] ^= rhs.v[i];
        }

        // Ensure that the bits past the end of the bitfield are zeroed
        if min_len.bit() != 0 {
            let last = (self.v[end - 1] >> min_len.cbit()) << min_len.cbit();
            self.v[end - 1] = last;
        }

        // Update the length in case `self` was truncated
        self.length = min_len;
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
        let end = self.length.ceil().byte();
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
    /// Bits that are dropped off the left side are wrapped around to fill the right side.
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

        // let crhs = 8 - rhs;
        // let max_bit = self.max_index().bit() as usize;

        // let mut res = Vec::<u8>::new();
        // for i in 0..(self.max_index().byte() - 1) {
        //     res.push((self.v[i] << rhs) | (self.v[i + 1] >> crhs));
        // }

        // let i = self.max_index().byte() - 1;
        // if rhs <= max_bit {
        //     res.push((self.v[i] << rhs) | (self.v[i + 1] >> crhs));
        //     if max_bit != 0 {
        //         res.push((self.v[i + 1] << rhs) | (((self.v[0] >> crhs) << crhs) >> (max_bit - rhs)));
        //     }
        // } else if max_bit != 0 {
        //     res.push((self.v[i] << rhs) | (self.v[i + 1] >> crhs) | (self.v[0] >> (crhs + max_bit)));
        //     res.push((self.v[0] >> crhs) << (8 - max_bit));
        // } else {
        //     res.push((self.v[i] << rhs) | (self.v[0] >> crhs));
        // }

        let shift = BitIndex::bits(rhs);
        

        let mut v = Vec::<u8>::with_capacity(self.v.len());


        for i in 0..self.v.len() {
            let bi = BitIndex::bytes(i) + shift;
            v.push(self.extract_u8_cyclical(bi));
        }

        if !self.length.is_byte_boundary() {
            v[self.length.byte()] = (v[self.length.byte()] >> self.length.cbit()) << self.length.cbit();
        }
        
        BitField {v: v, length: self.len()}
    }

}

impl std::ops::ShlAssign<usize> for BitField  {

    /// Transforms `self` by shifting all bits to the left by `rhs` bits.
    /// Bits that are dropped off the left side are wrapped around to fill the right side.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("1100 0000 1111 00");
    /// bf <<= 2;
    /// assert_eq!(bf, BitField::from_bin_str("0000 0011 1100 11"));
    /// bf <<= 4;
    /// assert_eq!(bf, BitField::from_bin_str("0011 1100 1100 00"));
    ///```
    fn shl_assign(&mut self, rhs: usize){
        *self = std::mem::take(self) << rhs;
    }
}



impl std::ops::Shr<usize> for BitField {
    type Output = Self;

    /// Returns a [`BitField`](crate::BitField) with the bits shifted right by `rhs` bits.
    /// Bits that are dropped off the right side are wrapped around to fill the left side.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let bf = BitField::from_bin_str("1100 0000 1111 00");
    /// let bf = bf >> 2;
    /// assert_eq!(bf, BitField::from_bin_str("0011 0000 0011 11"));
    /// let bf = bf >> 4;
    /// assert_eq!(bf, BitField::from_bin_str("1111 0011 0000 00"));
    ///```
    fn shr(self, rhs: usize) -> Self::Output {
        if rhs == 0 {
            return self;
        }

        let shift = BitIndex::bits(rhs);
        // println!("{:?}", shift);

        let mut v = Vec::<u8>::with_capacity(self.v.len());


        for i in 0..self.v.len() {
            let bi = BitIndex::bytes(i) - shift;
            v.push(self.extract_u8_cyclical(bi));
        }

        if !self.length.is_byte_boundary() {
            v[self.length.byte()] = (v[self.length.byte()] >> self.length.cbit()) << self.length.cbit();
        }
        
        BitField::new(v, self.length)
    }

}

impl std::ops::ShrAssign<usize> for BitField  {

    /// Transforms `self` by shifting all bits to the right by `rhs` bits.
    /// Bits that are dropped off the right side are wrapped around to fill the right side.
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BitField, BitIndex};
    ///
    /// let mut bf = BitField::from_bin_str("1100 0000 1111 00");
    /// bf >>= 2;
    /// assert_eq!(bf, BitField::from_bin_str("0011 0000 0011 11"));
    /// bf >>= 4;
    /// assert_eq!(bf, BitField::from_bin_str("1111 0011 0000 00"));
    ///```
    fn shr_assign(&mut self, rhs: usize){
        *self = std::mem::take(self) >> rhs;
    }
}

pub trait FromBitField {
    fn from_bf_be(bf: &BitField) -> Self;
    fn from_bf_le(bf: &BitField) -> Self;
}

impl FromBitField for u8 {

    fn from_bf_be(bf: &BitField) -> u8 {
        let b = bf.len().bit();
        if b == 0 {
            bf.v[0]
        } else {
            bf.v[0] >> (8 - b)
        }
    }

    fn from_bf_le(bf: &BitField) -> u8 {
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
        assert_eq!(BitField::zeros(BitIndex::new(2, 4)), BitField::from_bin_str("0000 0000 0000 0000 0000"));
        assert_eq!(BitField::zeros(BitIndex::new(3, 0)), BitField::from_bin_str("0000 0000 0000 0000 0000 0000"));
        assert_eq!(BitField::zeros(BitIndex::new(0, 0)), BitField::from_bin_str(""));
    }

    #[test]
    fn ones() {
        assert_eq!(BitField::ones(BitIndex::new(2, 4)), BitField::from_bin_str("1111 1111 1111 1111 1111"));
        assert_eq!(BitField::ones(BitIndex::new(3, 0)), BitField::from_bin_str("1111 1111 1111 1111 1111 1111"));
        assert_eq!(BitField::ones(BitIndex::new(0, 0)), BitField::from_bin_str(""));
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
        bf.truncate(BitIndex::new(2, 2));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1010 11"));
        bf.truncate(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 1010"));
        bf.truncate(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 10"));
        bf.truncate(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 10"));
        bf.truncate(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 0000 10"));
        bf.truncate(BitIndex::new(1, 2));
        assert_eq!(bf, BitField::from_bin_str("0101 1111 00"));
        bf.truncate(BitIndex::new(0, 2));
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
    fn crc_test() {
        let bf = BitField::from_bin_str("11010011101100");
        assert_eq!(bf.crc_be(BitField::from_bin_str("000"), BitField::from_bin_str("011")), BitField::from_bin_str("100"));
        let bf = BitField::from_hex_str("E100CAFE");
        assert_eq!(bf.crc_be(BitField::from_bin_str("00000000"), BitField::from_bin_str("00110001")), BitField::from_bin_str("00100011"));
        assert_eq!(bf.crc_be(BitField::from_bin_str("0000000"), BitField::from_bin_str("0110001")), BitField::from_bin_str("0000001"));
        assert_eq!(bf.crc_be(BitField::from_bin_str("000000"), BitField::from_bin_str("011001")), BitField::from_bin_str("101100"));
        assert_eq!(bf.crc_be(BitField::from_bin_str("00000"), BitField::from_bin_str("01001")), BitField::from_bin_str("01010"));

        let bf = BitField::from_hex_str("01E100CAFE");
        assert_eq!(bf.crc_be(BitField::from_bin_str("00000"), BitField::from_bin_str("01001")), BitField::from_bin_str("11000"));

        let bf = BitField::from_hex_str("CAFE");
        assert_eq!(bf.crc_be(BitField::from_bin_str("00000000000000000"), BitField::from_bin_str("010 0101 1011 1011 01")), BitField::from_bin_str("1000 1001 1111 1111 0"));

        let bf = BitField::from_bin_str("11101010");
        assert_eq!((bf.crc_be(BitField::from_bin_str("00000000"), BitField::from_bin_str("00000111"))), BitField::from_bin_str("10011000"));

        // let bf = BitField::from_hex_str("49 48 44 52 00 00 00 20 00 00 00 20 08 02 00 00 00");
        // let bf = BitField::from_hex_str("92 12 22 4A 00 00 00 04 00 00 00 04 10 40 00 00 00");
        // let bf = BitField::from_hex_str("00 00 00 40 10 04 00 00 00 04 00 00 00 4A 22 12 92");
        // assert_eq!(!&(bf.crc(BitField::from_hex_str("04C11DB7"))), BitField::from_hex_str("FC18EDA3"));
        // assert_eq!((bf.crc(BitField::from_hex_str("2083B8ED"))), BitField::from_hex_str("FC18EDA3"));
        // assert_eq!((bf.crc(BitField::from_hex_str("EDB88320"))), BitField::from_hex_str("FC18EDA3"));
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
    fn bitwise_assign() {
        let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100 0011");
        let bf2 = BitField::from_bin_str("1010 1100 1100 1001 1010 0011");
        let mut bf3 = bf1.clone();
        bf3 &= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("0000 1100 0000 1000 1000 0011"));
        bf3 = bf1.clone();
        bf3 |= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("1111 1111 1100 1011 1110 0011"));
        bf3 = bf1.clone();
        bf3 ^= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("1111 0011 1100 0011 0110 0000"));

        let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100");
        let bf2 = BitField::from_bin_str("1010 1100 1100 1001 1010 0011");
        bf3 = bf1.clone();
        bf3 &= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("0000 1100 0000 1000 1000"));
        bf3 = bf1.clone();
        bf3 |= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("1111 1111 1100 1011 1110"));
        bf3 = bf1.clone();
        bf3 ^= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("1111 0011 1100 0011 0110"));

        let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100 0011");
        let bf2 = BitField::from_bin_str("1010 1100 1100 1001 1010");
        bf3 = bf1.clone();
        bf3 &= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("0000 1100 0000 1000 1000"));
        bf3 = bf1.clone();
        bf3 |= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("1111 1111 1100 1011 1110"));
        bf3 = bf1.clone();
        bf3 ^= &bf2;
        assert_eq!(bf3, BitField::from_bin_str("1111 0011 1100 0011 0110"));
    }

    #[test]
    fn shifts() {
        let bf = BitField::from_vec(vec![0x00, 0x00, 0xAB, 0x0F]);
        assert_eq!(bf.clone() << 2, BitField::from_vec(vec![0x00, 0x02, 0xAC, 0x3C]));
        assert_eq!(bf.clone() << 4, BitField::from_vec(vec![0x00, 0x0A, 0xB0, 0xF0]));
        assert_eq!(bf.clone() << 12, BitField::from_vec(vec![0x0A, 0xB0, 0xF0, 0x00]));
        assert_eq!(bf.clone() << 6, (bf.clone() << 4) << 2);
        assert_eq!(bf.clone() << 0, bf.clone());

        assert_eq!(bf.clone() >> 2, BitField::from_vec(vec![0xC0, 0x00, 0x2A, 0xC3]));
        assert_eq!(bf.clone() >> 4, BitField::from_vec(vec![0xF0, 0x00, 0x0A, 0xB0]));
        assert_eq!(bf.clone() >> 6, (bf.clone() >> 4) >> 2);
        assert_eq!(bf.clone() >> 0, bf.clone());

        // let bf = BitField::from_bin_str("1100 0000 1111 00");
        // let bf = bf >> 2;
        // assert_eq!(bf, BitField::from_bin_str("0011 0000 0011 11"));
        // let bf = bf >> 4;
        // assert_eq!(bf, BitField::from_bin_str("1100 1100 0000 11"));
        let bf = BitField::from_hex_str("AB CD EF 7");
        assert_eq!(bf.clone() >> 4, BitField::from_hex_str("7A BC DE F"));
        assert_eq!(bf.clone() >> 12, BitField::from_hex_str("EF 7A BC D"));
    }

    #[test]
    fn left_shifts() {
        let bf = BitField::from_vec(vec![0x00, 0x00, 0xAB, 0x0F]);
        assert_eq!(bf.clone() << 2, BitField::from_vec(vec![0x00, 0x02, 0xAC, 0x3C]));
        assert_eq!(bf.clone() << 4, BitField::from_vec(vec![0x00, 0x0A, 0xB0, 0xF0]));
        assert_eq!(bf.clone() << 6, (bf.clone() << 4) << 2);
        assert_eq!(bf.clone() << 12, BitField::from_vec(vec![0x0A, 0xB0, 0xF0, 0x00]));
        assert_eq!(bf.clone() << 76, BitField::from_vec(vec![0x0A, 0xB0, 0xF0, 0x00]));
        assert_eq!(bf.clone() << 0, bf.clone());
        assert_eq!(bf.clone() << 64, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011");
        assert_eq!(bf.clone() << 2, BitField::from_bin_str("1011 1100 0001 0100 1110"));
        assert_eq!(bf.clone() << 4, BitField::from_bin_str("1111 0000 0101 0011 1010"));
        assert_eq!(bf.clone() << 6, BitField::from_bin_str("1100 0001 0100 1110 1011"));
        assert_eq!(bf.clone() << 26, BitField::from_bin_str("1100 0001 0100 1110 1011"));
        assert_eq!(bf.clone() << 46, BitField::from_bin_str("1100 0001 0100 1110 1011"));
        assert_eq!(bf.clone() << 206, BitField::from_bin_str("1100 0001 0100 1110 1011"));
        assert_eq!(bf.clone() << 20, bf.clone());
        assert_eq!(bf.clone() << 200, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 01");
        assert_eq!(bf.clone() << 1, BitField::from_bin_str("010 1111 0000 0101 011"));
        assert_eq!(bf.clone() << 3, BitField::from_bin_str("0 1111 0000 0101 01101"));
        assert_eq!(bf.clone() << 5, BitField::from_bin_str("111 0000 0101 011010 1"));
        assert_eq!(bf.clone() << 23, BitField::from_bin_str("111 0000 0101 011010 1"));
        assert_eq!(bf.clone() << 185, BitField::from_bin_str("111 0000 0101 011010 1"));
        assert_eq!(bf.clone() << 18, bf.clone());
        assert_eq!(bf.clone() << 180, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011 11");
        assert_eq!(bf.clone() << 2, BitField::from_bin_str("1011 1100 0001 0100 1111 10"));
        assert_eq!(bf.clone() << 4, BitField::from_bin_str("1111 0000 0101 0011 1110 10"));
        assert_eq!(bf.clone() << 6, BitField::from_bin_str("1100 0001 0100 1111 1010 11"));
        assert_eq!(bf.clone() << 28, BitField::from_bin_str("1100 0001 0100 1111 1010 11"));
        assert_eq!(bf.clone() << 446, BitField::from_bin_str("1100 0001 0100 1111 1010 11"));
        assert_eq!(bf.clone() << 22, bf.clone());
        assert_eq!(bf.clone() << 440, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011 110");
        assert_eq!(bf.clone() << 1 << 2 << 3 << 4 << 5 << 6 << 7, bf.clone() << 5);
        // println!("{:?}", bf.clone() << 6);
        // todo!();
        let bf = BitField::from_hex_str("AB CD EF 7");
        assert_eq!(bf.clone() << 4, BitField::from_hex_str("BC DE F7 A"));
        assert_eq!(bf.clone() << 12, BitField::from_hex_str("DE F7 AB C"));
    }

    #[test]
    fn right_shifts() {
        let bf = BitField::from_vec(vec![0x00, 0x00, 0xAB, 0x0F]);
        assert_eq!(bf.clone() >> 2, BitField::from_vec(vec![0xC0, 0x00, 0x2A, 0xC3]));
        assert_eq!(bf.clone() >> 4, BitField::from_vec(vec![0xF0, 0x00, 0x0A, 0xB0]));
        assert_eq!(bf.clone() >> 6, (bf.clone() >> 4) >> 2);
        assert_eq!(bf.clone() >> 12, BitField::from_vec(vec![0xB0, 0xF0, 0x00, 0x0A]));
        assert_eq!(bf.clone() >> 76, BitField::from_vec(vec![0xB0, 0xF0, 0x00, 0x0A]));
        assert_eq!(bf.clone() >> 0, bf.clone());
        assert_eq!(bf.clone() >> 64, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011");
        assert_eq!(bf.clone() >> 2, BitField::from_bin_str("1110 1011 1100 0001 0100"));
        assert_eq!(bf.clone() >> 4, BitField::from_bin_str("0011 1010 1111 0000 0101"));
        assert_eq!(bf.clone() >> 6, BitField::from_bin_str("0100 1110 1011 1100 0001"));
        assert_eq!(bf.clone() >> 26, BitField::from_bin_str("0100 1110 1011 1100 0001"));
        assert_eq!(bf.clone() >> 46, BitField::from_bin_str("0100 1110 1011 1100 0001"));
        assert_eq!(bf.clone() >> 206, BitField::from_bin_str("0100 1110 1011 1100 0001"));
        assert_eq!(bf.clone() >> 20, bf.clone());
        assert_eq!(bf.clone() >> 200, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 01");
        assert_eq!(bf.clone() >> 1, BitField::from_bin_str("1101 0111 1000 0010 10"));
        assert_eq!(bf.clone() >> 3, BitField::from_bin_str("1011 0101 1110 0000 10"));
        assert_eq!(bf.clone() >> 5, BitField::from_bin_str("1010 1101 0111 1000 00"));
        assert_eq!(bf.clone() >> 23, BitField::from_bin_str("1010 1101 0111 1000 00"));
        assert_eq!(bf.clone() >> 185, BitField::from_bin_str("1010 1101 0111 1000 00"));
        assert_eq!(bf.clone() >> 18, bf.clone());
        assert_eq!(bf.clone() >> 180, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011 11");
        assert_eq!(bf.clone() >> 2, BitField::from_bin_str("1110 1011 1100 0001 0100 11"));
        assert_eq!(bf.clone() >> 4, BitField::from_bin_str("1111 1010 1111 0000 0101 00"));
        assert_eq!(bf.clone() >> 6, BitField::from_bin_str("0011 1110 1011 1100 0001 01"));
        assert_eq!(bf.clone() >> 28, BitField::from_bin_str("0011 1110 1011 1100 0001 01"));
        assert_eq!(bf.clone() >> 446, BitField::from_bin_str("0011 1110 1011 1100 0001 01"));
        assert_eq!(bf.clone() >> 22, bf.clone());
        assert_eq!(bf.clone() >> 440, bf.clone());

        let bf = BitField::from_bin_str("1010 1111 0000 0101 0011 110");
        assert_eq!(bf.clone() >> 1 >> 2 >> 3 >> 4 >> 5 >> 6 >> 7, bf.clone() >> 5);
        // println!("{:?}", bf.clone() << 6);
        // todo!();
        let bf = BitField::from_hex_str("AB CD EF 7");
        assert_eq!(bf.clone() >> 4, BitField::from_hex_str("7A BC DE F"));
        assert_eq!(bf.clone() >> 12, BitField::from_hex_str("EF 7A BC D"));
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

    /*
    #[test]
    fn slices_le() {
        let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100 0011 0110 1001");
        let bf2 = BitField::from_bin_str("0110 1001 1100 0011 0000 1010 0101 1111");
        for i in 0..32 {
            for j in i..32 {
                let start = BitIndex::bits(i);
                let end = BitIndex::bits(j+1);
                let mut be_slice = bf1.slice_be(&start, &end);
                be_slice.pad_unsigned_be(BitIndex::bits(32));
                let mut le_slice = bf2.slice_le2(&start, &end);
                le_slice.pad_unsigned_le(BitIndex::bits(32));
                assert_eq!(u32::from_be_bytes(be_slice.into_array().unwrap()), u32::from_le_bytes(le_slice.into_array().unwrap()))
                
            }
        }

        // let bf1 = BitField::from_bin_str("0101 1111 0000 1010 1100 0011 0110 1001 011");
        // let mut bf2 = bf1.clone();
        // bf2.swap_be_to_le();
        // for i in 0..35 {
        //     for j in i..35 {
        //         let start = BitIndex::bits(i);
        //         let end = BitIndex::bits(j+1);
        //         let mut be_slice = bf1.slice_be(&start, &end);
        //         be_slice.pad_unsigned_be(BitIndex::bits(32));
        //         let mut le_slice = bf2.slice_le2(&start, &end);
        //         le_slice.pad_unsigned_le(BitIndex::bits(32));
        //         assert_eq!(u32::from_be_bytes(be_slice.into_array().unwrap()), u32::from_le_bytes(le_slice.into_array().unwrap()))
                
        //     }
        // }
    }
    */

    #[test]
    fn float_tests() {
        let frac: u32 = 4788187;
        let exp: u8 = 128;

        let bf = BitField::from_vec(frac.to_be_bytes().to_vec());
        let mut bf2 = BitField::zeros(BitIndex::new(0, 1));
        bf2.extend(&BitField::from_vec(vec![exp]));
        bf2.extend(&BitField::zeros(BitIndex::bits(23)));
        bf2 = &bf2 | &bf;
        let result = f32::from_be_bytes(bf2.clone().into_array().unwrap());
        assert_eq!(result, std::f32::consts::PI);
        let mut frac_slice = bf2.slice_be(&BitIndex::bits(9), &BitIndex::bits(32));
        frac_slice.pad_unsigned_be(BitIndex::bits(32));
        assert_eq!(u32::from_be_bytes(frac_slice.into_array().unwrap()), frac);
        let exp_slice = bf2.slice_be(&BitIndex::bits(1), &BitIndex::bits(9));
        assert_eq!(u8::from_be_bytes(exp_slice.into_array().unwrap()), exp);
        // panic!("{}", result)
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

        let bf = BitField::from_bin_str("0011 1000 1010 0101 11");
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(0, 0)), 0x38);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(0, 2)), 0xe2);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(0, 4)), 0x8a);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(0, 6)), 0x29);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(1, 0)), 0xa5);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(1, 2)), 0x97);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(1, 4)), 0x5c);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(1, 6)), 0x73);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(2, 0)), 0xce);

        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(2, 2)), 0x38);
        assert_eq!(bf.extract_u8_cyclical(BitIndex::new(3, 4)), 0x97);

        assert_eq!(bf.extract_u8_cyclical(-BitIndex::new(0, 4)), 0x73);
    }

    #[test]
    fn pad_unsigned() {
        let mut bf = BitField::from_bin_str("1010 0011 10");
        bf.pad_unsigned_le(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 010"));
        bf.pad_unsigned_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0010"));
        bf.pad_unsigned_le(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0001 0"));
        bf.pad_unsigned_le(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 10"));
        bf.pad_unsigned_le(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 010"));
        bf.pad_unsigned_le(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0010"));

        bf.pad_unsigned_le(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0010 0000"));
        bf.pad_unsigned_le(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0010 0000 0000"));

        let mut bf = BitField::from_bin_str("1010 0011");
        bf.pad_unsigned_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000"));

        let mut bf = BitField::from_bin_str("1010 0011 10");
        bf.pad_unsigned_be(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("0101 0001 110"));
        bf.pad_unsigned_be(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("0010 1000 1110"));
        bf.pad_unsigned_be(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("0001 0100 0111 0"));
        bf.pad_unsigned_be(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("0000 1010 0011 10"));
        bf.pad_unsigned_be(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("0000 0101 0001 110"));
        bf.pad_unsigned_be(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("0000 0010 1000 1110"));

        bf.pad_unsigned_be(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("0000 0000 0010 1000 1110"));
        bf.pad_unsigned_be(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("0000 0000 0000 0010 1000 1110"));

        let mut bf = BitField::from_bin_str("1010 0011");
        bf.pad_unsigned_be(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("0000 1010 0011"));
    }

    #[test]
    fn pad_twos_compliment() {
        // Negative little-endian
        let mut bf = BitField::from_bin_str("1010 0011 10");
        bf.pad_twos_compliment_le(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 110"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1110"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1111 0"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1111 10"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1111 110"));
        bf.pad_twos_compliment_le(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1111 1110"));

        bf.pad_twos_compliment_le(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1111 1110 1111"));
        bf.pad_twos_compliment_le(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1111 1110 1111 1111"));

        let mut bf = BitField::from_bin_str("1010 0011");
        bf.pad_twos_compliment_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1111"));

        // Positive little-endian
        let mut bf = BitField::from_bin_str("1010 0011 01");
        bf.pad_twos_compliment_le(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 001"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0001"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 1"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 01"));
        bf.pad_twos_compliment_le(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 001"));
        bf.pad_twos_compliment_le(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0001"));

        bf.pad_twos_compliment_le(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0001 0000"));
        bf.pad_twos_compliment_le(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0001 0000 0000"));

        let mut bf = BitField::from_bin_str("0110 0011");
        bf.pad_twos_compliment_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("0110 0011 0000"));
    }

    #[test]
    fn pad_sign_magnitude() {
        // Negative big-endian
        let mut bf = BitField::from_bin_str("1010 0011 10");
        bf.pad_sign_magnitude_be(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("1001 0001 110"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1000 1000 1110"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("1000 0100 0111 0"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("1000 0010 0011 10"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("1000 0001 0001 110"));
        bf.pad_sign_magnitude_be(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("1000 0000 1000 1110"));

        bf.pad_sign_magnitude_be(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("1000 0000 0000 1000 1110"));
        bf.pad_sign_magnitude_be(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("1000 0000 0000 0000 1000 1110"));

        let mut bf = BitField::from_bin_str("1010 0011");
        bf.pad_sign_magnitude_be(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1000 0010 0011"));

        // Positive big-endian
        let mut bf = BitField::from_bin_str("0110 0011 10");
        bf.pad_sign_magnitude_be(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("0011 0001 110"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("0001 1000 1110"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("0000 1100 0111 0"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("0000 0110 0011 10"));
        bf.pad_sign_magnitude_be(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("0000 0011 0001 110"));
        bf.pad_sign_magnitude_be(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("0000 0001 1000 1110"));

        bf.pad_sign_magnitude_be(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("0000 0000 0001 1000 1110"));
        bf.pad_sign_magnitude_be(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("0000 0000 0000 0001 1000 1110"));

        let mut bf = BitField::from_bin_str("0110 0011");
        bf.pad_sign_magnitude_be(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("0000 0110 0011"));

        // Negative little-endian
        let mut bf = BitField::from_bin_str("1010 0011 10");
        bf.pad_sign_magnitude_le(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 100"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1000"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1000 0"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1000 00"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1000 000"));
        bf.pad_sign_magnitude_le(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 1000 0000"));

        bf.pad_sign_magnitude_le(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0000 1000"));
        bf.pad_sign_magnitude_le(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0000 1000 0000"));

        let mut bf = BitField::from_bin_str("1010 0011");
        bf.pad_sign_magnitude_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("0010 0011 1000"));

        // Positive little-endian
        let mut bf = BitField::from_bin_str("1010 0011 01");
        bf.pad_sign_magnitude_le(BitIndex::new(1, 3));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 001"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0001"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 5));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 1"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 6));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 01"));
        bf.pad_sign_magnitude_le(BitIndex::new(1, 7));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 001"));
        bf.pad_sign_magnitude_le(BitIndex::new(2, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0001"));

        bf.pad_sign_magnitude_le(BitIndex::new(2, 4));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0001 0000"));
        bf.pad_sign_magnitude_le(BitIndex::new(3, 0));
        assert_eq!(bf, BitField::from_bin_str("1010 0011 0000 0001 0000 0000"));

        let mut bf = BitField::from_bin_str("0110 0011");
        bf.pad_sign_magnitude_le(BitIndex::new(1, 4));
        assert_eq!(bf, BitField::from_bin_str("0110 0011 0000"));
    }

    #[test]
    fn int_conversions_be() {
        let mut bf = BitField::from_hex_str("00 01 e2 40"); // +123456 in sign-magnitude
        assert_eq!(bf.convert_unsigned_be(IntFormat::SignMagnitude), false);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("00 01 e2 40"); // +123456 in sign-magnitude
            bf.pad_sign_magnitude_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::SignMagnitude), false);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("80 01 e2 40"); // -123456 in sign-magnitude
        assert_eq!(bf.convert_unsigned_be(IntFormat::SignMagnitude), true);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("80 01 e2 40"); // -123456 in sign-magnitude
            bf.pad_sign_magnitude_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::SignMagnitude), true);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("00 01 e2 40"); // +123456 in two's complement
        assert_eq!(bf.convert_unsigned_be(IntFormat::TwosCompliment), false);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("00 01 e2 40"); // +123456 in two's complement
            bf.pad_twos_compliment_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::TwosCompliment), false);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("ff fe 1d c0"); // -123456 in two's complement
        assert_eq!(bf.convert_unsigned_be(IntFormat::TwosCompliment), true);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("ff fe 1d c0"); // -123456 in two's complement
            bf.pad_twos_compliment_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::TwosCompliment), true);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("00 01 e2 40"); // +123456 in one's complement
        assert_eq!(bf.convert_unsigned_be(IntFormat::OnesCompliment), false);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("00 01 e2 40"); // +123456 in one's complement
            bf.pad_twos_compliment_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::OnesCompliment), false);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("ff fe 1d bf"); // -123456 in one's complement
        assert_eq!(bf.convert_unsigned_be(IntFormat::OnesCompliment), true);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("ff fe 1d bf"); // -123456 in one's complement
            bf.pad_twos_compliment_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::OnesCompliment), true);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("00 06 26 40"); // +123456 in base -2
        assert_eq!(bf.convert_unsigned_be(IntFormat::BaseMinusTwo), false);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);


        for i in 32..64 {
            let mut bf = BitField::from_hex_str("00 06 26 40"); // +123456 in base -2
            bf.pad_unsigned_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::BaseMinusTwo), false);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("00 02 62 c0"); // -123456 in base -2
        assert_eq!(bf.convert_unsigned_be(IntFormat::BaseMinusTwo), true);
        assert_eq!(u32::from_be_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("00 02 62 c0"); // -123456 in base -2
            bf.pad_unsigned_be(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_be(IntFormat::BaseMinusTwo), true);
            bf.pad_unsigned_be(BitIndex::new(8, 0));
            assert_eq!(u64::from_be_bytes(bf.into_array().unwrap()), 123456);
        }
    }

    #[test]
    fn int_conversions_le() {
        let mut bf = BitField::from_hex_str("40 e2 01 00"); // +123456 in sign-magnitude
        assert_eq!(bf.convert_unsigned_le(IntFormat::SignMagnitude), false);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("40 e2 01 00"); // +123456 in sign-magnitude
            bf.pad_sign_magnitude_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::SignMagnitude), false);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("40 e2 01 80"); // -123456 in sign-magnitude
        assert_eq!(bf.convert_unsigned_le(IntFormat::SignMagnitude), true);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("40 e2 01 80"); // -123456 in sign-magnitude
            bf.pad_sign_magnitude_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::SignMagnitude), true);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("40 e2 01 00"); // +123456 in two's complement
        assert_eq!(bf.convert_unsigned_le(IntFormat::TwosCompliment), false);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("40 e2 01 00"); // +123456 in two's complement
            bf.pad_twos_compliment_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::TwosCompliment), false);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("c0 1d fe ff"); // -123456 in two's complement
        assert_eq!(bf.convert_unsigned_le(IntFormat::TwosCompliment), true);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("c0 1d fe ff"); // -123456 in two's complement
            bf.pad_twos_compliment_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::TwosCompliment), true);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("40 e2 01 00"); // +123456 in one's complement
        assert_eq!(bf.convert_unsigned_le(IntFormat::OnesCompliment), false);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("40 e2 01 00"); // +123456 in one's complement
            bf.pad_twos_compliment_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::OnesCompliment), false);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("bf 1d fe ff"); // -123456 in one's complement
        assert_eq!(bf.convert_unsigned_le(IntFormat::OnesCompliment), true);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("bf 1d fe ff"); // -123456 in one's complement
            bf.pad_twos_compliment_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::OnesCompliment), true);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("40 26 06 00"); // +123456 in base -2
        assert_eq!(bf.convert_unsigned_le(IntFormat::BaseMinusTwo), false);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);


        for i in 32..64 {
            let mut bf = BitField::from_hex_str("40 26 06 00"); // +123456 in base -2
            bf.pad_unsigned_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::BaseMinusTwo), false);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }

        let mut bf = BitField::from_hex_str("c0 62 02 00"); // -123456 in base -2
        assert_eq!(bf.convert_unsigned_le(IntFormat::BaseMinusTwo), true);
        assert_eq!(u32::from_le_bytes(bf.into_array().unwrap()), 123456);

        for i in 32..64 {
            let mut bf = BitField::from_hex_str("c0 62 02 00"); // -123456 in base -2
            bf.pad_unsigned_le(BitIndex::bits(i));
            assert_eq!(bf.convert_unsigned_le(IntFormat::BaseMinusTwo), true);
            bf.pad_unsigned_le(BitIndex::new(8, 0));
            assert_eq!(u64::from_le_bytes(bf.into_array().unwrap()), 123456);
        }
    }
}  