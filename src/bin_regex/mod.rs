//! Provides routines for searching binary data structures (implementing [`BitIndexable`](crate::BitIndexable)) for specified patterns
//!
//! # Syntax
//!
//! ### Basic Matches
//!<pre class="rust">
//! _        => Matches single 0 bit
//! '        => Matches single 1 bit
//! .        => Matches any single bit
//! !        => Matches any byte
//! 0-f      => Matches corresponding nibble (case insensitive)
//!</pre>
//!
//! ### Achors
//!<pre class="rust">
//! :        => Matches byte boundary
//! ;        => Matches nibble boundary
//!</pre>
//!
//! ### Repetitions
//!<pre class="rust">
//! *        => Causes RE to match zero or more repetitions of the preceding group (greedy)
//! +        => Causes RE to match one or more repetitions of the preceding group (greedy)
//! ?        => Causes RE to match zero or one repetitions of the preceding group (greedy)
//! {n}      => Causes RE to match exactly n repetitions of the preceding group
//! {n,}     => Causes RE to match n or more repetitions of the preceding group (greedy)
//! {n,m}    => Causes RE to match between n and m repetitions of the preceding group (greedy)
//! *?       => Causes RE to match zero or more repetitions of the preceding group (lazy)
//! +?       => Causes RE to match one or more repetitions of the preceding group (lazy)
//! ??       => Causes RE to match zero or one repetitions of the preceding group (lazy)
//! {n}?     => Same as {n}
//! {n,}?    => Causes RE to match n or more repetitions of the preceding group (lazy)
//! {n,m}?   => Causes RE to match between n and m repetitions of the preceding group (lazy)
//!</pre>
//!
//! ### Groups
//!<pre class="rust">
//! (exp)    => Numbered capture group
//! (?<name>exp) => Named (also numbered) capture group
//! (?:exp)  => Non-capturing group
//!</pre>
//!
//! ### Character Classes
//!<pre class="rust">
//! [a8:xyzA-Z3-9]    => 8-bit ASCII
//! [u8:1,2,3,4..10]  => 8-bit unsigned integer
//! [i8:1,2,3,4..10]  => 8-bit two's compliment integer
//! [o8:1,2,3,4..10]  => 8-bit one's compliment integer
//! [s8:1,2,3,4..10]  => 8-bit sign-magnitude integer
//! [n8:1,2,3,4..10]  => 8-bit negabinary integer
//!</pre>
//!
//! # Compositions
//!<pre class="rust">
//! x|y      => Matches x or y
//! xy       => Matches x followed by y
//!</pre>

use std::collections::HashSet;

mod parse_helpers;
use crate::bin_regex::parse_helpers::{EscapeIter, escape_vec, find_right_delimiter};

use crate::bx;
use crate::bit_index::{BitIndex, BitIndexable};
use crate::bit_field::{IntFormat, BitField, FromBitField};

#[derive(Debug, Clone, PartialEq)]
enum Greediness {
    Greedy,
    Lazy
}

#[derive(Debug, Clone, PartialEq)]
enum Repeat {
    Exactly(usize),
    LessThan(usize, Greediness),
    Any(Greediness)
}

#[derive(Debug, Clone, PartialEq)]
enum GroupType {
    NonCapturing,
    Numbered,
    Named(String)
}


#[derive(Debug, PartialEq)]
enum DynamicCharacterClass {
    UInt(CharClass<UInt>),
    TwosCompInt(CharClass<TwosCompInt>),
    OnesCompInt(CharClass<OnesCompInt>),
    SignMagInt(CharClass<SignMagInt>),
    NegaInt(CharClass<NegaInt>)
}

impl DynamicCharacterClass {
    fn input_length(&self) -> BitIndex {
        match self {
            DynamicCharacterClass::UInt(cls) => cls.input_length(),
            DynamicCharacterClass::TwosCompInt(cls) => cls.input_length(),
            DynamicCharacterClass::OnesCompInt(cls) => cls.input_length(),
            DynamicCharacterClass::SignMagInt(cls) => cls.input_length(),
            DynamicCharacterClass::NegaInt(cls) => cls.input_length()
        }
    }

    fn matches(&self, input: &BitField) -> bool {
        match self {
            DynamicCharacterClass::UInt(cls) => cls.matches(input),
            DynamicCharacterClass::TwosCompInt(cls) => cls.matches(input),
            DynamicCharacterClass::OnesCompInt(cls) => cls.matches(input),
            DynamicCharacterClass::SignMagInt(cls) => cls.matches(input),
            DynamicCharacterClass::NegaInt(cls) => cls.matches(input)
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Repetition(Repeat, Box<Token>),
    Group(Option<usize>, Vec<Token>),
    Choice(Vec<Token>),
    CharacterClass(std::rc::Rc<DynamicCharacterClass>),
    Nibble(u8),
    ByteBoundary,
    NibbleBoundary,
    BitZero,
    BitOne,
    BitAny,
    ByteAny,
}

#[derive(Debug, Clone)]
enum StateFlag {
    GroupStart(usize),
    GroupEnd(usize),
    NotOffsetAnd(usize) // Proceeds if (offset & value) == 0
}

#[derive(Debug, Clone)]
enum StateTransition {
    Free,
    EqualsBit(u8),
    EqualsNibble(u8),
    ConsumeBits(usize),
    CharacterClass(std::rc::Rc<DynamicCharacterClass>)
}

enum TextEncoding {
    Ascii,
    Utf8,
    Utf16,
    Hex
}

// trait CharClass: std::fmt::Debug {
//     fn input_length(&self) -> BitIndex;
//     fn matches(&self, input: &BitField) -> bool;
// }

// enum CharClassType {
//     Ascii,
//     UInt(usize),
//     IInt(usize)
// }

// #[derive(PartialEq, Eq, Debug)]
// struct U8CharClass {
//     inverted: bool,
//     options: HashSet<UInt>,
//     ranges: Vec<(u8, u8)>
// }

// impl CharClass for U8CharClass {
//     fn input_length(&self) -> BitIndex {BitIndex::new(1, 0)}
//     fn matches(&self, input: &BitField) -> bool {
//         let x = input.extract_u8(BitIndex::new(0, 0));
//         if self.options.contains(&x) {
//             return !self.inverted
//         }
//         for (start, end) in &self.ranges {
//             if *start <= x && x <= *end {
//                 return !self.inverted
//             }
//         }
//         return self.inverted
//     }
// }

// #[derive(std::hash::Hash, Debug)]
// struct UInt {
//     inner: u128
// }

// impl std::str::FromStr for UInt {
//     type Err = std::num::ParseIntError;

//     fn from_str(s: &str) -> Result<Self, Self::Err> {
//         Ok(UInt{inner: u128::from_str(s)?})
//     }
// }

#[derive(PartialEq, Eq, Ord, std::hash::Hash, Clone, Debug)]
struct UInt(u128);

impl FromBitField for UInt {
    fn from_bf_be(bf: &BitField) -> UInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            bf.pad_unsigned_be(BitIndex::bits(128));
        }

        UInt(u128::from_be_bytes(bf.into_array().unwrap()))
    }

    fn from_bf_le(bf: &BitField) -> UInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            bf.pad_unsigned_le(BitIndex::bits(128));
        }

        UInt(u128::from_le_bytes(bf.into_array().unwrap()))
    }
}

impl std::str::FromStr for UInt {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(UInt(u128::from_str(s)?))
    }
}

impl std::cmp::PartialOrd for UInt {
    fn partial_cmp(&self, other: &UInt) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

#[derive(PartialEq, Eq, Ord, std::hash::Hash, Clone, Debug)]
struct TwosCompInt(i128);

impl FromBitField for TwosCompInt {
    fn from_bf_be(bf: &BitField) -> TwosCompInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            bf.pad_twos_compliment_be(BitIndex::bits(128));
        }

        TwosCompInt(i128::from_be_bytes(bf.into_array().unwrap()))
    }

    fn from_bf_le(bf: &BitField) -> TwosCompInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            bf.pad_twos_compliment_le(BitIndex::bits(128));
        }

        TwosCompInt(i128::from_le_bytes(bf.into_array().unwrap()))
    }
}

impl std::str::FromStr for TwosCompInt {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(TwosCompInt(i128::from_str(s)?))
    }
}

impl std::cmp::PartialOrd for TwosCompInt {
    fn partial_cmp(&self, other: &TwosCompInt) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

#[derive(PartialEq, Eq, Ord, std::hash::Hash, Clone, Debug)]
struct OnesCompInt(i128);

impl FromBitField for OnesCompInt {
    fn from_bf_be(bf: &BitField) -> OnesCompInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            // Two's compliment padding and one's compliment padding are the same
            bf.pad_twos_compliment_be(BitIndex::bits(128));
        }

        let neg = bf.convert_unsigned_be(IntFormat::OnesCompliment);
        let mut i = u128::from_be_bytes(bf.into_array().unwrap()) as i128;
        if neg {
            i *= -1
        }
        OnesCompInt(i)
    }

    fn from_bf_le(bf: &BitField) -> OnesCompInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            // Two's compliment padding and one's compliment padding are the same
            bf.pad_twos_compliment_le(BitIndex::bits(128));
        }

        let neg = bf.convert_unsigned_le(IntFormat::OnesCompliment);
        let mut i = u128::from_le_bytes(bf.into_array().unwrap()) as i128;
        if neg {
            i *= -1
        }
        OnesCompInt(i)
    }
}

impl std::str::FromStr for OnesCompInt {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(OnesCompInt(i128::from_str(s)?))
    }
}

impl std::cmp::PartialOrd for OnesCompInt {
    fn partial_cmp(&self, other: &OnesCompInt) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

#[derive(PartialEq, Eq, Ord, std::hash::Hash, Clone, Debug)]
struct SignMagInt(i128);

impl FromBitField for SignMagInt {
    fn from_bf_be(bf: &BitField) -> SignMagInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            bf.pad_sign_magnitude_be(BitIndex::bits(128));
        }

        let neg = bf.convert_unsigned_be(IntFormat::SignMagnitude);
        let mut i = u128::from_be_bytes(bf.into_array().unwrap()) as i128;
        if neg {
            i *= -1
        }
        SignMagInt(i)
    }

    fn from_bf_le(bf: &BitField) -> SignMagInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            bf.pad_sign_magnitude_le(BitIndex::bits(128));
        }

        let neg = bf.convert_unsigned_le(IntFormat::SignMagnitude);
        let mut i = u128::from_le_bytes(bf.into_array().unwrap()) as i128;
        if neg {
            i *= -1
        }
        SignMagInt(i)
    }
}

impl std::str::FromStr for SignMagInt {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(SignMagInt(i128::from_str(s)?))
    }
}

impl std::cmp::PartialOrd for SignMagInt {
    fn partial_cmp(&self, other: &SignMagInt) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

#[derive(PartialEq, Eq, Ord, std::hash::Hash, Clone, Debug)]
struct NegaInt(i128);

impl FromBitField for NegaInt {
    fn from_bf_be(bf: &BitField) -> NegaInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            // Unsigned padding and negabinary padding are the same
            bf.pad_unsigned_be(BitIndex::bits(128));
        }

        let neg = bf.convert_unsigned_be(IntFormat::BaseMinusTwo);
        let mut i = u128::from_be_bytes(bf.into_array().unwrap()) as i128;
        if neg {
            i *= -1
        }
        NegaInt(i)
    }

    fn from_bf_le(bf: &BitField) -> NegaInt {
        let mut bf = bf.clone();
        let n = bf.len().total_bits();
        if n > 128 {
            bf.truncate(BitIndex::bits(128));
        } else if n < 128 {
            // Unsigned padding and negabinary padding are the same
            bf.pad_unsigned_le(BitIndex::bits(128));
        }

        let neg = bf.convert_unsigned_le(IntFormat::BaseMinusTwo);
        let mut i = u128::from_le_bytes(bf.into_array().unwrap()) as i128;
        if neg {
            i *= -1
        }
        NegaInt(i)
    }
}

impl std::str::FromStr for NegaInt {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(NegaInt(i128::from_str(s)?))
    }
}

impl std::cmp::PartialOrd for NegaInt {
    fn partial_cmp(&self, other: &NegaInt) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

#[derive(PartialEq, Eq, Debug)]
enum Endian {
    Big,
    Little
}

#[derive(PartialEq, Eq, Debug)]
struct CharClass<T: std::str::FromStr + Ord + std::hash::Hash + FromBitField> {
    inverted: bool,
    endian: Endian,
    options: HashSet<T>,
    ranges: Vec<(T, T)>,
    input_length: BitIndex
}

impl<T: std::str::FromStr + Ord + std::hash::Hash + FromBitField + std::fmt::Debug> CharClass<T> {
    fn input_length(&self) -> BitIndex {
        self.input_length
    }

    fn matches(&self, input: &BitField) -> bool {
        let x: T = match self.endian {
            Endian::Big => T::from_bf_be(input),
            Endian::Little => T::from_bf_le(input)
        };
        //println!("TRYING TO MATCH {:?}", x);
        if self.options.contains(&x) {
            return !self.inverted
        }
        for (start, end) in &self.ranges {
            if *start <= x && x <= *end {
                return !self.inverted
            }
        }
        return self.inverted
    }
}

fn parse_ascii_char_class(input: &Vec<char>, endian: Endian) -> Result<CharClass<UInt>, String> {
    let mut input_iter = escape_vec(input).peekable();
    let mut options = HashSet::<UInt>::new();
    let mut ranges = Vec::<(UInt, UInt)>::new();
    let mut prev_char: Option<UInt> = None;
    // let mut escaped = false;
    let mut range_started = false;

    let inverted = if input_iter.peek() == Some(&('^', false)) {
        input_iter.next();
        true
    } else {
        false
    };

    for (c, escaped) in input_iter {
        match c {
            '-' if !escaped => {
                match prev_char {
                    Some(_) if range_started => return Err("Unexpected '-' encountered after '-'".to_string()),
                    Some(_) => {
                        range_started = true;
                        continue
                    },
                    None => return Err("Unexpected '-' encountered at beginning of character class".to_string()),
                }
            },
            _ if range_started => {
                match prev_char {
                    Some(ref p) => {
                        ranges.push((p.clone(), UInt(c as u128)));
                        prev_char = None;
                    },
                    None => return Err("Impossible state".to_string())
                }
            },
            _ => {
                match prev_char {
                    Some(ref p) => {
                        options.insert(p.clone());
                    },
                    None => ()
                }
                prev_char = Some(UInt(c as u128));
            }
        }
        range_started = false;

    }
    match prev_char {
        Some(ref p) => {
            options.insert(p.clone());
        },
        None => ()
    }
    Ok(CharClass::<UInt> {inverted, endian, options, ranges, input_length: BitIndex::new(1, 0)})
}

enum RangeParseProgress<T: std::str::FromStr + Ord + std::hash::Hash + FromBitField + std::fmt::Debug> {
    NotStarted,
    OneDot(T),
    TwoDot(T)
}

fn parse_int_char_class<T: std::str::FromStr + Ord + std::hash::Hash + FromBitField + std::fmt::Debug>(input: &Vec<char>, nbits: usize, endian: Endian) -> Result<CharClass<T>, String>
where <T as std::str::FromStr>::Err: std::fmt::Display {
    let input_length = bx!(,nbits);
    let mut input_iter = escape_vec(input).peekable();
    let mut options = HashSet::<T>::new();
    let mut ranges = Vec::<(T, T)>::new();
    let mut prev_word = Vec::<char>::new();
    let mut range_prog = RangeParseProgress::<T>::NotStarted;

    let inverted = if input_iter.peek() == Some(&('^', false)) {
        input_iter.next();
        true
    } else {
        false
    };

    for (c, escaped) in input_iter {
        if escaped {
            return Err("Escaped characters invalid in decimal character class".to_string());
        }
        match c {
            ',' => {
                println!("Prev word: {}", prev_word.iter().collect::<String>());
                match prev_word.iter().collect::<String>().parse::<T>() {
                    Ok(n) => {
                        match range_prog {
                            RangeParseProgress::NotStarted => {
                                options.insert(n);
                            },
                            RangeParseProgress::TwoDot(n0) => {
                                ranges.push((n0, n));
                                range_prog = RangeParseProgress::NotStarted;
                            },
                            _ => return Err(format!("Encountered unexpected character '{}' while parsing range", c))
                        }
                    },
                    Err(msg) => return Err(msg.to_string())
                }
                prev_word.clear();
            },
            '.' => {
                match range_prog {
                    RangeParseProgress::NotStarted => {
                        println!("Prev word: {}", prev_word.iter().collect::<String>());
                        match prev_word.iter().collect::<String>().parse::<T>() {
                            Ok(n) => {
                                range_prog = RangeParseProgress::OneDot(n);
                                prev_word.clear();
                            },
                            Err(msg) => return Err(msg.to_string())
                        }
                    },
                    RangeParseProgress::OneDot(n0) => {
                        if !prev_word.is_empty() {
                            return Err("Impossible State".to_string())
                        }
                        range_prog = RangeParseProgress::TwoDot(n0);
                    },
                    RangeParseProgress::TwoDot(_) => {
                        return Err(format!("Encountered unexpected character '{}' while parsing range", c))
                    }
                }
            },
            '-' | '+' | '0'..='9' => {
                match range_prog {
                    RangeParseProgress::OneDot(_) => {
                        return Err(format!("Encountered unexpected character '{}' while parsing range", c))
                    },
                    _ => ()
                }
                prev_word.push(c);
            },
            _ => return Err(format!("Encountered unexpected character '{}' while parsing decimal character class", c))
        }

    }

    if prev_word.is_empty() {
        return Err("Encountered end of character class before expected".to_string())
    }
    println!("Last word: '{}'", prev_word.iter().collect::<String>());
    match prev_word.iter().collect::<String>().parse::<T>() {
        Ok(n) => {
            match range_prog {
                RangeParseProgress::NotStarted => {
                    options.insert(n);
                },
                RangeParseProgress::TwoDot(n0) => {
                    ranges.push((n0, n));
                },
                _ => return Err("Encountered end of character class before expected".to_string())
            }
        },
        Err(msg) => return Err(msg.to_string())
    }

    Ok(CharClass::<T> {inverted, endian, options, ranges, input_length})
}

fn parse_char_class(input: &Vec<char>) -> Result<Token, String> {
    let mut from_start = Vec::<char>::new();
    for (i, c) in input.iter().enumerate() {
        match c {
            '<' | '>' | '0'..='9'|'a'..='z'|'A'..='Z' => {
                from_start.push(*c);
            },
            ':' => {
                let mut char_class_type_index = 0;
                let endian = match from_start[0] {
                    '<' => {
                        char_class_type_index += 1;
                        Endian::Little
                    },
                    '>' => {
                        char_class_type_index += 1;
                        Endian::Big
                    },
                    _ => Endian::Big
                };

                match from_start[(char_class_type_index + 1)..].iter().collect::<String>().parse::<usize>() {
                    Ok(n) => {
                        match from_start[char_class_type_index] {
                            'a' => {
                                let cls_result = parse_ascii_char_class(&input[i+1..].to_vec(), endian);
                                match cls_result {
                                    Ok(cls) => {
                                        return Ok(Token::CharacterClass(std::rc::Rc::new(DynamicCharacterClass::UInt(cls))))
                                    },
                                    Err(msg) => return Err(msg)
                                }
                            },
                            'u' => {
                                let cls_result = parse_int_char_class::<UInt>(&input[i+1..].to_vec(), n, endian);
                                match cls_result {
                                    Ok(cls) => {
                                        return Ok(Token::CharacterClass(std::rc::Rc::new(DynamicCharacterClass::UInt(cls))))
                                    },
                                    Err(msg) => return Err(msg)
                                }
                            },
                            'i' => {
                                let cls_result = parse_int_char_class::<TwosCompInt>(&input[i+1..].to_vec(), n, endian);
                                match cls_result {
                                    Ok(cls) => {
                                        return Ok(Token::CharacterClass(std::rc::Rc::new(DynamicCharacterClass::TwosCompInt(cls))))
                                    },
                                    Err(msg) => return Err(msg)
                                }
                            },
                            'o' => {
                                let cls_result = parse_int_char_class::<OnesCompInt>(&input[i+1..].to_vec(), n, endian);
                                match cls_result {
                                    Ok(cls) => {
                                        return Ok(Token::CharacterClass(std::rc::Rc::new(DynamicCharacterClass::OnesCompInt(cls))))
                                    },
                                    Err(msg) => return Err(msg)
                                }
                            },
                            's' => {
                                let cls_result = parse_int_char_class::<SignMagInt>(&input[i+1..].to_vec(), n, endian);
                                match cls_result {
                                    Ok(cls) => {
                                        return Ok(Token::CharacterClass(std::rc::Rc::new(DynamicCharacterClass::SignMagInt(cls))))
                                    },
                                    Err(msg) => return Err(msg)
                                }
                            },
                            'n' => {
                                let cls_result = parse_int_char_class::<NegaInt>(&input[i+1..].to_vec(), n, endian);
                                match cls_result {
                                    Ok(cls) => {
                                        return Ok(Token::CharacterClass(std::rc::Rc::new(DynamicCharacterClass::NegaInt(cls))))
                                    },
                                    Err(msg) => return Err(msg)
                                }
                            },
                            _ => return Err(format!("Character class type '{}' not recognized", from_start.iter().collect::<String>()))
                        }
                    },
                    Err(msg) => return Err(msg.to_string())
                }
            },
            _ => break
        }
    }
    match parse_ascii_char_class(input, Endian::Big) {
        Ok(cls) => {
            Ok(Token::CharacterClass(std::rc::Rc::new(DynamicCharacterClass::UInt(cls))))
        },
        Err(msg) => Err(msg)
    }
}

fn compile(input: &Vec<Token>, start_index: usize) -> Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>> {
    let mut result = Vec::<Vec<(usize, StateTransition, Vec<StateFlag>)>>::new();
    let mut i = start_index;
    for token in input {
        match token {
            Token::Repetition(Repeat::Any(greediness), inside) => {
                let inside_result = compile(&vec![*inside.clone()], i + 1);
                let inside_len = inside_result.len();
                match greediness {
                    Greediness::Greedy => {
                        result.push(vec![(i + 1, StateTransition::Free, vec![]), (i + inside_len + 2, StateTransition::Free, vec![])]);
                        result.extend(inside_result);
                        result.push(vec![(i + 1, StateTransition::Free, vec![]), (i + inside_len + 2, StateTransition::Free, vec![])]);
                    },
                    Greediness::Lazy => {
                        result.push(vec![(i + inside_len + 2, StateTransition::Free, vec![]), (i + 1, StateTransition::Free, vec![])]);
                        result.extend(inside_result);
                        result.push(vec![(i + inside_len + 2, StateTransition::Free, vec![]), (i + 1, StateTransition::Free, vec![])]);
                    }
                }

                i += inside_len + 2;
            },
            Token::Repetition(Repeat::Exactly(n), inside) => {
                for _ in 0..*n {
                    let inside_result = compile(&vec![*inside.clone()], i);
                    i += inside_result.len();
                    result.extend(inside_result);
                }
            },
            Token::Repetition(Repeat::LessThan(n, greediness), inside) => {
                let start_i = i - start_index;
                result.push(Vec::<(usize, StateTransition, Vec<StateFlag>)>::new());
                i += 1;
                for _ in 0..(*n - 1) {
                    result[start_i].push((i, StateTransition::Free, vec![]));
                    let inside_result = compile(&vec![*inside.clone()], i);
                    i += inside_result.len();
                    result.extend(inside_result);
                }
                result[start_i].push((i, StateTransition::Free, vec![]));
                if matches!(greediness, Greediness::Lazy) {
                    result[start_i].reverse();
                }
            },
            Token::Choice(inside) => {
                let mut finish_indices = Vec::<usize>::new();
                let start_i = i - start_index;
                result.push(Vec::<(usize, StateTransition, Vec<StateFlag>)>::new());
                i += 1;
                for tok in inside {
                    result[start_i].push((i, StateTransition::Free, vec![]));
                    let inside_result = compile(&vec![tok.clone()], i);
                    i += inside_result.len();
                    result.extend(inside_result);
                    result.push(Vec::<(usize, StateTransition, Vec<StateFlag>)>::new());
                    finish_indices.push(i - start_index);
                    i += 1;
                }
                for finish_i in finish_indices {
                    result[finish_i].push((i, StateTransition::Free, vec![]));
                }

            },
            Token::Group(Some(group_index), inside) => {
                let inside_result = compile(inside, i + 1);
                let inside_len = inside_result.len();
                result.push(vec![(i + 1, StateTransition::Free, vec![StateFlag::GroupStart(*group_index)])]);
                result.extend(inside_result);
                result.push(vec![(i + inside_len + 2, StateTransition::Free, vec![StateFlag::GroupEnd(*group_index)])]);
                i += inside_len + 2;
            },
            Token::Group(None, inside) => {
                let inside_result = compile(inside, i);
                let inside_len = inside_result.len();
                result.extend(inside_result);
                i += inside_len;
            },
            Token::CharacterClass(cls) => {
                result.push(vec![(i + 1, StateTransition::CharacterClass(cls.clone()), vec![])]);
                i += 1;
            }
            Token::BitZero => {
                result.push(vec![(i + 1, StateTransition::EqualsBit(0), vec![])]);
                i += 1;
            },
            Token::BitOne => {
                result.push(vec![(i + 1, StateTransition::EqualsBit(1), vec![])]);
                i += 1;
            },
            Token::BitAny => {
                result.push(vec![(i + 1, StateTransition::ConsumeBits(1), vec![])]);
                i += 1;
            },
            Token::Nibble(n) => {
                result.push(vec![(i + 1, StateTransition::EqualsNibble(*n), vec![])]);
                i += 1;
            }
            Token::ByteAny => {
                result.push(vec![(i + 1, StateTransition::ConsumeBits(8), vec![])]);
                i += 1;
            },
            Token::ByteBoundary => {
                result.push(vec![(i + 1, StateTransition::Free, vec![StateFlag::NotOffsetAnd(0x07)])]);
                i += 1;
            },
            Token::NibbleBoundary => {
                result.push(vec![(i + 1, StateTransition::Free, vec![StateFlag::NotOffsetAnd(0x03)])]);
                i += 1;
            }
        }
    }
    result
}

fn normalize_index(removed: &Vec<usize>, index: usize) -> usize {
    let mut result = index;
    for r in removed {
        if *r < index {
            result -= 1;
        }
    }
    result
}

fn get_direct_transitions(fsm: &Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>>, state: usize) -> Vec<(usize, StateTransition, Vec<StateFlag>)> {
    let mut result = Vec::<(usize, StateTransition, Vec<StateFlag>)>::new();
    let mut explorer_state = state;
    let mut path = Vec::<(usize, usize)>::new(); // state, transition index
    let mut sum_flags = Vec::<Vec<StateFlag>>::new();
    let mut t_index = 0;
    let final_depth = fsm.len();
    println!("Processing state {}", state);
    loop {
        let mut transitions = &fsm[explorer_state];
        println!("{} {:?}", t_index, path);
        while t_index >= transitions.len() { // If we're out of transitions, start backtracking
            sum_flags.pop();
            match path.pop() {
                Some((dest, i)) => {
                    println!("Backtracking");
                    explorer_state = dest;
                    transitions = &fsm[explorer_state];
                    t_index = i;
                },
                None => return result // If we've explored every path and we're back at the root, return
            }
        }
        match &transitions[t_index] {
            (dest, StateTransition::Free, flags) if *dest != final_depth => { // If it's a free transition, go deeper
                println!("\tDeeper to state {}", dest);
                if path.contains(&(explorer_state, t_index + 1)) {
                    t_index += 1;
                    continue // If the path takes a loop, leave that option out of the final list.
                }
                path.push((explorer_state, t_index + 1));
                sum_flags.push(flags.to_vec());
                explorer_state = *dest;
                t_index = 0;
                continue
            },
            (dest, t, final_flags) => { // If it's not a free transition, record it
                println!("\tRecording state transition {} {}", state, t_index);
                let mut new_flags = Vec::<StateFlag>::new();
                for flags in &sum_flags {
                    new_flags.extend(flags.to_vec());
                }
                new_flags.extend(final_flags.to_vec());
                result.push((*dest, t.clone(), new_flags));
                t_index += 1;
            }
        }
    }
}

fn remove_dead_states(fsm: &mut Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>>) {
    let mut valid_states = HashSet::new();
    valid_states.insert(0);
    for transitions in fsm.iter() {
        for (dest, _t, _flags) in transitions {
            valid_states.insert(*dest);
        }
    }
    let n_states = fsm.len();
    let mut removed = Vec::<usize>::new();
    for state in 0..n_states {
        if !valid_states.contains(&state) {
            removed.push(state);
        }
    }

    removed.reverse();

    for r in &removed {
        fsm.remove(*r);
    }

    for transitions in fsm.iter_mut() {
        for transition in transitions {
            transition.0 = normalize_index(&removed, transition.0);
        }
    }

}

fn optimize(fsm: &mut Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>>) {

    let n_states = fsm.len();
    for state in 0..n_states {
        let new_transitions = get_direct_transitions(fsm, state);
        fsm[state] = new_transitions;
    }

    println!("{:?}", fsm);

    remove_dead_states(fsm);

}

fn tokenize(pattern: &str) -> Result<(Vec<Token>, usize, std::collections::HashMap<String, usize>), String> {
    let char_vec: Vec<char> = pattern.chars().collect();
    tokenize_vec(&char_vec, 1)
}

fn parse_group_header(input: &[char]) -> Result<(GroupType, usize), String> {
    let mut input_iter = input.iter();
    match &input_iter.next() {
        Some('?') => {
            match &input_iter.next() {
                Some('<') => {
                    let mut name = Vec::<char>::new();
                    let mut offset = 2;
                    for c in input_iter {
                        match c {
                            '>' => {
                                return Ok((GroupType::Named(name.into_iter().collect::<String>()), offset + 1));
                            },
                            _ => name.push(*c)
                        }
                        offset += 1;
                    }
                    Err("Unterminated group name".to_string())
                },
                Some(':') => {
                    Ok((GroupType::NonCapturing, 2))
                },
                _ => Err("'?' at beginning of group".to_string())
            }
        },
        _ => Ok((GroupType::Numbered, 0))
    }
}

fn tokenize_vec(char_vec: &Vec<char>, start_group: usize) -> Result<(Vec<Token>, usize, std::collections::HashMap<String, usize>), String> {
    let mut result = Vec::<Token>::new();
    let mut i = 0;
    let mut option_flag = false;
    let mut groups_map = std::collections::HashMap::new();
    let mut group_index = start_group;
    loop {
        if i >= char_vec.len() {
            break
        }
        let result_len = result.len();
        match char_vec[i] {
            '_' => result.push(Token::BitZero),
            '\'' => result.push(Token::BitOne),
            '.' => result.push(Token::BitAny),
            '!' => result.push(Token::ByteAny),
            ':' => result.push(Token::ByteBoundary),
            ';' => result.push(Token::NibbleBoundary),
            '?' => {
                match result.pop() {
                    Some(last) => {
                        let mut greediness = Greediness::Greedy;
                        if i + 1 < char_vec.len() && char_vec[i + 1] == '?' {
                            greediness = Greediness::Lazy;
                            i += 1;
                        }
                        result.push(Token::Repetition(Repeat::LessThan(2, greediness), Box::new(last)));
                    },
                    None => return Err("Encountered '?' at beginning of group".to_string())
                }
            },
            '*' => {
                match result.pop() {
                    Some(last) => {
                        let mut greediness = Greediness::Greedy;
                        if i + 1 < char_vec.len() && char_vec[i + 1] == '?' {
                            greediness = Greediness::Lazy;
                            i += 1;
                        }
                        result.push(Token::Repetition(Repeat::Any(greediness), Box::new(last)));
                    },
                    None => return Err("Encountered '*' at beginning of group".to_string())
                }
            },
            '+' => {
                if result.is_empty() {
                    return Err("Encountered '+' at beginning of group".to_string())
                } else {
                    let mut greediness = Greediness::Greedy;
                    if i + 1 < char_vec.len() && char_vec[i + 1] == '?' {
                        greediness = Greediness::Lazy;
                        i += 1;
                    }
                    let last = result[result.len() - 1].clone();
                    result.push(Token::Repetition(Repeat::Any(greediness), Box::new(last)))
                }
            },
            '|' => {
                option_flag = true;
            },
            '[' => {
                match find_right_delimiter(char_vec, i, '[', ']') {
                    Some(end_index) => {
                        match parse_char_class(&char_vec[i+1..end_index].to_vec()) {
                            Ok(token) => result.push(token),
                            Err(msg) => return Err(msg)
                        }
                        i = end_index;
                    },
                    None => return Err("Unclosed opening delimiter '['".to_string())
                }
            },
            '{' => {
                match find_right_delimiter(char_vec, i, '{', '}') {
                    Some(end_index) => {
                        let inside = &char_vec[i+1..end_index];
                        i = end_index;

                        let mut greediness = Greediness::Greedy;
                        if i + 1 < char_vec.len() && char_vec[i + 1] == '?' {
                            greediness = Greediness::Lazy;
                            i += 1;
                        }

                        match inside.iter().position(|x| *x == ',') {
                            Some(sep) => {
                                if sep + 1 == inside.len() { // {n,}
                                    match inside[..sep].iter().collect::<String>().parse::<usize>() {
                                        Ok(n) => {
                                            match result.pop() {
                                                Some(last) => {
                                                    result.push(Token::Repetition(Repeat::Exactly(n), Box::new(last.clone())));
                                                    result.push(Token::Repetition(Repeat::Any(greediness), Box::new(last)));
                                                },
                                                None => return Err("Encountered '{' at beginning of group".to_string())
                                            }
                                        },
                                        Err(msg) => return Err(msg.to_string())
                                    }
                                } else { // {n,m}
                                    match (inside[..sep].iter().collect::<String>().parse::<usize>(),
                                            inside[1+sep..].iter().collect::<String>().parse::<usize>())
                                    {
                                        (Ok(n), Ok(m)) => {
                                            match result.pop() {
                                                Some(last) => {
                                                    result.push(Token::Repetition(Repeat::Exactly(n), Box::new(last.clone())));
                                                    result.push(Token::Repetition(Repeat::LessThan(m - n + 1, greediness), Box::new(last)));
                                                },
                                                None => return Err("Encountered '{' at beginning of group".to_string())
                                            }
                                        },
                                        (Err(msg), _) => return Err(msg.to_string()),
                                        (_, Err(msg)) => return Err(msg.to_string()),
                                    }
                                }
                            },
                            None => { // {n}
                                match inside.iter().collect::<String>().parse::<usize>() {
                                    Ok(n) => {
                                        match result.pop() {
                                            Some(last) => result.push(Token::Repetition(Repeat::Exactly(n), Box::new(last))),
                                            None => return Err("Encountered '{' at beginning of group".to_string())
                                        }
                                    },
                                    Err(msg) => return Err(msg.to_string())
                                } 
                            }
                        }
                    },
                    None => return Err("Unclosed opening delimiter '{'".to_string())
                }
            },
            '(' => {
                match find_right_delimiter(char_vec, i, '(', ')') {
                    Some(end_index) => {
                        match parse_group_header(&char_vec[i+1..end_index]) {
                            Ok((GroupType::Numbered, start_index)) => {
                                match tokenize_vec(&char_vec[i+1+start_index..end_index].to_vec(), group_index + 1) {
                                    Ok((tokens, new_groups, new_groups_map)) => {
                                        result.push(Token::Group(Some(group_index), tokens));
                                        group_index += new_groups + 1;
                                        for (key, val) in new_groups_map.iter() {
                                            if groups_map.contains_key(key) {
                                                return Err(format!("Group name '{}' used more than once", key))
                                            } else {
                                                groups_map.insert(key.clone(), *val);
                                            }
                                        }
                                    },
                                    Err(msg) => return Err(msg)
                                } 
                                i = end_index;
                            },
                            Ok((GroupType::Named(name), start_index)) => {
                                if groups_map.contains_key(&name) {
                                    return Err(format!("Group name '{}' used more than once", name))
                                } else {
                                    groups_map.insert(name, group_index);
                                }
                                match tokenize_vec(&char_vec[i+1+start_index..end_index].to_vec(), group_index + 1) {
                                    Ok((tokens, new_groups, new_groups_map)) => {
                                        result.push(Token::Group(Some(group_index), tokens));
                                        group_index += new_groups + 1;
                                        for (key, val) in new_groups_map.iter() {
                                            if groups_map.contains_key(key) {
                                                return Err(format!("Group name '{}' used more than once", key))
                                            } else {
                                                groups_map.insert(key.clone(), *val);
                                            }
                                        }
                                    },
                                    Err(msg) => return Err(msg)
                                } 
                                i = end_index;
                            },
                            Ok((GroupType::NonCapturing, start_index)) => {
                                match tokenize_vec(&char_vec[i+1+start_index..end_index].to_vec(), group_index) {
                                    Ok((tokens, new_groups, new_groups_map)) => {
                                        result.push(Token::Group(None, tokens));
                                        group_index += new_groups;
                                        for (key, val) in new_groups_map.iter() {
                                            if groups_map.contains_key(key) {
                                                return Err(format!("Group name '{}' used more than once", key))
                                            } else {
                                                groups_map.insert(key.clone(), *val);
                                            }
                                        }
                                    },
                                    Err(msg) => return Err(msg)
                                } 
                                i = end_index;
                            },
                            _ => todo!()
                        }

                    },
                    None => return Err("Unclosed opening delimiter '('".to_string())
                }
            },
            c => {
                match c {
                    '0'..='9' => {
                        result.push(Token::Nibble(c as u8 - 48));
                    },
                    'a'..='f' => {
                        result.push(Token::Nibble(c as u8 - 87));
                    },
                    'A'..='F' => {
                        result.push(Token::Nibble(c as u8 - 55));
                    },
                    _ => return Err(format!("Encountered unexpected character '{}'", c))
                }
            }
        }
        if option_flag && result.len() != result_len { // If a token was added after the option delimiter was spotted
            match result.pop() {
                Some(last) => {
                    match result.pop() {
                        Some(Token::Choice(options)) => {
                            let mut options = options.to_vec();
                            options.push(last);
                            result.push(Token::Choice(options));
                            option_flag = false;
                        },
                        Some(token) => {
                            result.push(Token::Choice(vec![token, last]));
                            option_flag = false;
                        },
                        None => return Err("Encountered unexpected character '|'".to_string())
                    }
                },
                None => return Err("Encountered '|' at beginning of group".to_string())
            }
        }
        i += 1;
    }
    Ok((result, group_index - start_group, groups_map))
}

fn check_state_flags<T: BitIndexable>(input: &T, flags: &Vec<StateFlag>, offset: BitIndex) -> bool {
    for flag in flags {
        match flag {
            StateFlag::GroupStart(_) | StateFlag::GroupEnd(_) => (),
            StateFlag::NotOffsetAnd(value) => {
                if (offset.bit() as usize & value) != 0 {
                    return false
                }
            }
        }
    }
    true
}


/// Structure to contain a single [`BinRegex`](crate::bin_regex::BinRegex) match.
///
/// # Examples
/// ```rust
/// use bitutils2::{BinRegex, BitIndex};
///
/// let input = vec![0x00, 0x0A, 0xBC, 0xD0, 0xAB];
///
/// let mut re = BinRegex::new(".*A(BC)(F?)").unwrap();
///
/// let cap = re.captures(&input).unwrap();
///
/// let m0 = cap.get(0).unwrap();
/// assert_eq!(m0.start(), BitIndex::new(0, 0));
/// assert_eq!(m0.end(), BitIndex::new(3, 0));
/// assert_eq!(m0.span(), (BitIndex::new(0, 0), BitIndex::new(3, 0)));
/// assert_eq!(m0.is_empty(), false);
///
/// let m1 = cap.get(1).unwrap();
/// assert_eq!(m1.start(), BitIndex::new(2, 0));
/// assert_eq!(m1.end(), BitIndex::new(3, 0));
/// assert_eq!(m1.span(), (BitIndex::new(2, 0), BitIndex::new(3, 0)));
/// assert_eq!(m1.is_empty(), false);
///
/// let m2 = cap.get(2).unwrap();
/// assert_eq!(m2.start(), BitIndex::new(3, 0));
/// assert_eq!(m2.end(), BitIndex::new(3, 0));
/// assert_eq!(m2.span(), (BitIndex::new(3, 0), BitIndex::new(3, 0)));
/// assert_eq!(m2.is_empty(), true);
///```
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub struct BinMatch<'a, T: BitIndexable> {
    input: &'a T,
    start: BitIndex,
    end: BitIndex
}

impl<'a, T: BitIndexable> BinMatch<'a, T> {

    /// Basic constructor for structure
    pub fn new(input: &'a T, start: BitIndex, end: BitIndex) -> BinMatch<'a, T> {
        BinMatch {input, start, end}
    }

    /// Accesses the start index of the match
    pub fn start(&self) -> BitIndex {
        self.start
    }

    /// Accesses the end index of the match
    pub fn end(&self) -> BitIndex {
        self.end
    }

    /// Returns `true` if the match is empty (`start == end`)
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Returns a tuple with the start and end indices of the match
    pub fn span(&self) -> (BitIndex, BitIndex) {
        (self.start, self.end)
    }

    /// Returns the contents of the match as a [`BitField`](crate::BitField)
    pub fn as_bf(&self) -> BitField {
        self.input.bit_slice(&self.start, &self.end)
    }
}

/// Iterator that yields successive non-overlapping matches of the provided input.
/// There is no public constructor for this structure, instead users must use
/// [`BinRegex.find_iter`](crate::BinRegex::find_iter).
pub struct BinMatches<'a, T: BitIndexable> {
    gen: CapturePathGenerator<'a, T>,
    max_index: BitIndex,
    current_offset: BitIndex
}

impl<'a, T: BitIndexable> BinMatches<'a, T> {
    fn new(fsm: &'a Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>>, input: &'a T) -> BinMatches<'a, T> {
        let gen = CapturePathGenerator::new(fsm, input);
        let max_index = gen.input.max_index();
        BinMatches {gen, max_index, current_offset: BitIndex::new(0, 0)}
    }
}

impl<'a, T: BitIndexable> std::iter::Iterator for BinMatches<'a, T> {
    type Item = BinMatch<'a, T>;

    fn next(&mut self) -> Option<BinMatch<'a, T>> {
        while self.current_offset < self.max_index {
            self.gen.reset(self.current_offset);
            if let Some((_, initial_offset)) = self.gen.next() {
                let mut max_offset = initial_offset;
                loop {
                    match self.gen.next() {
                        Some((_, offset)) if offset > max_offset => {
                            max_offset = offset;
                        },
                        None => {
                            let res = Some(BinMatch::new(self.gen.input, self.current_offset, max_offset));
                            self.current_offset = max_offset;
                            return res
                        },
                        _ => ()
                    }
                }
            }
            self.current_offset += 1;
        }
        None
    }
}

/// Represents the capture groups from a single match
pub struct BinCaptures<'a, T: BitIndexable> {
    groups: Vec<Option<BinMatch<'a, T>>>,
    groups_map: &'a std::collections::HashMap<String, usize>
}

impl<'a, T: BitIndexable> BinCaptures<'a, T> {

    /// Returns the capture group associated with the index `i` if that group
    /// matched any part of the input. Returns `None` otherwise. Capture groups
    /// are numbered from left to right by the position of the left parenthesis,
    /// starting at 1. Group 0 refers to the entire match.
    pub fn get(&self, i: usize) -> Option<BinMatch<T>> {
        if i < self.groups.len() {
            match &self.groups[i] {
                Some(m) => Some(BinMatch::new(m.input, m.start, m.end)),
                None => None
            }
        } else {
            None
        }
    }

    /// Returns the capture group associated with the name `name` if a group
    /// with that name exists in the expression and matched any part of the
    /// input. Returns `None` otherwise.
    pub fn name(&self, name: &str) -> Option<BinMatch<T>> {
        match self.groups_map.get(&name.to_string()) {
            Some(index) => self.get(*index),
            None => None
        }
    }
}

struct CapturePathGenerator<'a, T: BitIndexable> {
    fsm: &'a Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>>,
    input: &'a T,
    current_path: Vec::<(usize, usize, BitIndex)>,
    max_offset: BitIndex,
    current_offset: BitIndex,
    current_state: usize,
    t_index: usize
}

impl<'a, T: BitIndexable> CapturePathGenerator<'a, T> {

    fn new(fsm: &'a Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>>, input: &'a T) -> CapturePathGenerator<'a, T> {
        CapturePathGenerator {
            fsm,
            input,
            current_path: Vec::<(usize, usize, BitIndex)>::new(),
            max_offset: input.max_index(),
            current_offset: BitIndex::new(0, 0),
            current_state: 0,
            t_index: 0
        }
    }

    fn reset(&mut self, offset: BitIndex) {
        self.current_path = Vec::<(usize, usize, BitIndex)>::new();
        self.current_offset = offset;
        self.current_state = 0;
        self.t_index = 0;
    }

    fn try_backtrack(&mut self) -> bool {
        // Backtracks if possible and returns true. If not possible, returns false.
        match self.current_path.pop() {
            Some((dest, i, new_offset)) => {
                self.current_state = dest;
                self.t_index = i + 1;
                self.current_offset = new_offset;
                true
            },
            None => false
        }
    }

    fn next(&mut self) -> Option<(Vec::<(usize, usize, BitIndex)>, BitIndex)> {
        self.try_backtrack();
        loop {
            let mut transitions = &self.fsm[self.current_state];
            loop {

                while self.t_index >= transitions.len() {
                    if !self.try_backtrack() {
                        return None
                    }
                    transitions = &self.fsm[self.current_state];
                }

                let (dest, transition, flags) = &transitions[self.t_index];
                if check_state_flags(self.input, flags, self.current_offset) {
                    match transition {
                        StateTransition::Free => {
                            self.current_path.push((self.current_state, self.t_index, self.current_offset));
                            self.current_state = *dest;
                            break;
                        },
                        StateTransition::EqualsBit(value) => {
                            if self.current_offset < self.max_offset && self.input.bit_at(&self.current_offset) == *value {
                                self.current_path.push((self.current_state, self.t_index, self.current_offset));
                                self.current_state = *dest;
                                self.current_offset += 1;
                                break;
                            }
                        },
                        StateTransition::ConsumeBits(n) => {
                            if self.current_offset + n <= self.max_offset {
                                self.current_path.push((self.current_state, self.t_index, self.current_offset));
                                self.current_state = *dest;
                                self.current_offset += n;
                                break;
                            }
                        },
                        StateTransition::EqualsNibble(n) => {
                            if self.current_offset + 3 < self.max_offset {
                                let n2 = (self.input.bit_at(&self.current_offset) << 3) | (self.input.bit_at(&(self.current_offset + 1)) << 2) | 
                                        (self.input.bit_at(&(self.current_offset + 2)) << 1) | self.input.bit_at(&(self.current_offset + 3));
                                if *n == n2 {
                                    self.current_path.push((self.current_state, self.t_index, self.current_offset));
                                    self.current_state = *dest;
                                    self.current_offset += 4;
                                    break;   
                                }
                            }                       
                        },
                        StateTransition::CharacterClass(cls) => {
                            let n = cls.input_length();
                            let end = self.current_offset + n;
                            if end <= self.max_offset {
                                let bf = self.input.bit_slice(&self.current_offset, &end);
                                println!("{:?}, {}", bf, cls.matches(&bf));
                                if cls.matches(&bf) {
                                    self.current_path.push((self.current_state, self.t_index, self.current_offset));
                                    self.current_state = *dest;
                                    self.current_offset = end;
                                    break;
                                }
                            }
                        }
                    }
                }
                
                self.t_index += 1;
            }
            self.t_index = 0;
            if self.current_state >= self.fsm.len() {

                return Some((self.current_path.clone(), self.current_offset))
            }
            
        }
    }
}

/// A compiled variation of regular expressions intended for searching binary data. A
/// [`BinRegex`](crate::BinRegex) can be used to search binary data for patterns
pub struct BinRegex {
    fsm: Vec<Vec<(usize, StateTransition, Vec<StateFlag>)>>,
    pub n_groups: usize,
    groups_map: std::collections::HashMap<String, usize>
}

impl BinRegex {

    /// Compiles a binary regular expression. Once compiled, this object can be used 
    /// repeatedly to search input buffers.
    pub fn new(pattern: &str) -> Result<BinRegex, String>{
        let (tokens, n_groups, groups_map) = tokenize(pattern)?;
        let n_groups = n_groups + 1;
        let mut fsm = compile(&tokens, 0);
        optimize(&mut fsm);
        println!("{:?}", groups_map);
        Ok(BinRegex {fsm, n_groups, groups_map})
    }


    fn match_path<'a, T>(&'a self, input: &'a T) -> Option<(Vec::<(usize, usize, BitIndex)>, BitIndex)> 
    where &'a T: BitIndexable {
        let mut gen = CapturePathGenerator::new(&self.fsm, &input);
        match gen.next() {
            Some((path, offset)) => {
                let mut max_offset = offset;
                let mut current_path = path;
                loop {
                    match gen.next() {
                        Some((path, offset)) if offset > max_offset => {
                            max_offset = offset;
                            current_path = path
                        },
                        None => return Some((current_path, max_offset)),
                        _ => ()
                    }
                }
            },
            None => None
        }
    }

    /// Searches for the first match in the input given, and if found returns a [`BinMatch`](crate::BinMatch)
    /// object corresponding to the match. If no match is found, returns `None`. 
    ///
    /// # Examples
    ///```rust
    /// use bitutils2::{BinRegex, BitIndex};
    ///
    /// let input = vec![0x00, 0x0a, 0xbc, 0x00, 0x00, 0x00, 0xff, 0x00];
    ///
    /// let re1 = BinRegex::new("ABC_{8,}''").unwrap();
    /// let m1 = re1.find(&input).unwrap();
    /// assert_eq!(m1.span(), (BitIndex::new(1, 4), BitIndex::new(6, 2)));
    ///
    /// let re2 = BinRegex::new("ABC_{8,}'_").unwrap();
    /// assert_eq!(re2.find(&input), None);
    ///```
    pub fn find<'a, T>(&'a self, input: &'a T) -> Option<BinMatch<T>> 
    where &'a T: BitIndexable, T: BitIndexable {
        let mut gen = CapturePathGenerator::new(&self.fsm, input);

        let mut i = BitIndex::new(0, 0);
        let max_index = input.max_index();
        while i < max_index {
            gen.reset(i);
            if let Some((_, initial_offset)) = gen.next() {
                let mut max_offset = initial_offset;
                loop {
                    match gen.next() {
                        Some((_, offset)) if offset > max_offset => {
                            max_offset = offset;
                        },
                        None => return Some(BinMatch::new(input, i, max_offset)),
                        _ => ()
                    }
                }
            }
            i += 1;
        }
        None
    }

    /// Returns an iterator that yields successive non-overlapping matches in the input buffer.
    pub fn find_iter<'a, T>(&'a self, input: &'a T) -> BinMatches<'a, T>
    where &'a T: BitIndexable, T: BitIndexable {
        BinMatches::new(&self.fsm, input)

    }

    pub fn match_length<'a, T>(&'a self, input: &'a T) -> Option<BitIndex> 
    where &'a T: BitIndexable {
        match self.match_path(input) {
            Some((_, offset)) => Some(offset),
            None => None
        }
    }

    pub fn captures<'a, T>(&'a self, input: &'a T) -> Option<BinCaptures<T>> 
    where &'a T: BitIndexable, T: BitIndexable {
        match self.match_path(input) {
            Some((mut path, offset)) => {
                println!("{:?}",path);
                let mut groups = Vec::<Option<BinMatch<T>>>::new();
                for _ in 0..self.n_groups {
                    groups.push(None);
                }

                let mut group_ends = std::collections::HashMap::new();
                path.reverse();
                for (state, t_index, offset) in path {
                    let mut flags = self.fsm[state][t_index].2.to_vec();
                    println!("{:?}", flags);
                    flags.reverse();
                    for flag in flags {
                        match flag {
                            StateFlag::GroupEnd(group_index) => {
                                group_ends.insert(group_index, offset);
                            },
                            StateFlag::GroupStart(group_index) => {
                                match &groups[group_index] {
                                    None => 
                                        match group_ends.get(&group_index) {
                                            Some(end_index) => groups[group_index] = Some(BinMatch::new(input, offset, *end_index)),
                                            None => panic!("Group start with no end")
                                        },
                                    Some(bin_match) if bin_match.is_empty() => { // It's okay to overwrite the last match if it's empty
                                        match group_ends.get(&group_index) {
                                            Some(end_index) if *end_index != offset => groups[group_index] = Some(BinMatch::new(input, offset, *end_index)),
                                            _ => ()
                                        }
                                    },
                                    _ => ()
                                }
                            },
                            _ => ()
                        }
                    }
                }
                groups[0] = Some(BinMatch::new(input, BitIndex::new(0, 0), offset));
                Some(BinCaptures {groups, groups_map: &self.groups_map})
            }
            None => None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uint_be_char_class() {
        let input = "u5:0,1,23".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: false, 
            endian: Endian::Big, 
            options: HashSet::from([UInt(0), UInt(1), UInt(23)]),
            ranges: vec![], 
            input_length: bx!(,5)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = ">u6:^0,1,23".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Big, 
            options: HashSet::from([UInt(0), UInt(1), UInt(23)]), 
            ranges: vec![], 
            input_length: bx!(,6)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = "u8:^0,50..64,1,23,100..128".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Big, 
            options: HashSet::from([UInt(0), UInt(1), UInt(23)]),  
            ranges: vec![(UInt(50),UInt(64)), (UInt(100), UInt(128))], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = ">u120:^0,51230..641234,1,23000,100..128".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Big,
            options: HashSet::from([UInt(0), UInt(1), UInt(23000)]),  
            ranges: vec![(UInt(51230),UInt(641234)), (UInt(100), UInt(128))], 
            input_length: bx!(,120)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));
    }

    #[test]
    fn uint_le_char_class() {
        let input = "<u5:0,1,23".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: false, 
            endian: Endian::Little, 
            options: HashSet::from([UInt(0), UInt(1), UInt(23)]),
            ranges: vec![], 
            input_length: bx!(,5)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = "<u6:^0,1,23".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Little, 
            options: HashSet::from([UInt(0), UInt(1), UInt(23)]), 
            ranges: vec![], 
            input_length: bx!(,6)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = "<u8:^0,50..64,1,23,100..128".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Little, 
            options: HashSet::from([UInt(0), UInt(1), UInt(23)]),  
            ranges: vec![(UInt(50),UInt(64)), (UInt(100), UInt(128))], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = "<u120:^0,51230..641234,1,23000,100..128".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Little,
            options: HashSet::from([UInt(0), UInt(1), UInt(23000)]),  
            ranges: vec![(UInt(51230),UInt(641234)), (UInt(100), UInt(128))], 
            input_length: bx!(,120)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));
    }

    #[test]
    fn twos_compliment_be_char_class() {
        let input = "i5:0,-1,+23".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::TwosCompInt(CharClass::<TwosCompInt>{
            inverted: false, 
            endian: Endian::Big, 
            options: HashSet::from([TwosCompInt(0), TwosCompInt(-1), TwosCompInt(23)]),
            ranges: vec![], 
            input_length: bx!(,5)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = ">i6:^+0,1,-23".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::TwosCompInt(CharClass::<TwosCompInt>{
            inverted: true, 
            endian: Endian::Big, 
            options: HashSet::from([TwosCompInt(0), TwosCompInt(1), TwosCompInt(-23)]), 
            ranges: vec![], 
            input_length: bx!(,6)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = "i8:^-0,-50..+64,-1,+23,-130..-100".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::TwosCompInt(CharClass::<TwosCompInt>{
            inverted: true, 
            endian: Endian::Big, 
            options: HashSet::from([TwosCompInt(0), TwosCompInt(-1), TwosCompInt(23)]),  
            ranges: vec![(TwosCompInt(-50), TwosCompInt(64)), (TwosCompInt(-130), TwosCompInt(-100))], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));

        let input = ">i120:^+0,-521230..-641234,1,-23000,+100..128".chars().collect();
        let res = parse_char_class(&input).unwrap();
        let cls = DynamicCharacterClass::TwosCompInt(CharClass::<TwosCompInt>{
            inverted: true, 
            endian: Endian::Big,
            options: HashSet::from([TwosCompInt(0), TwosCompInt(1), TwosCompInt(-23000)]),  
            ranges: vec![(TwosCompInt(-521230), TwosCompInt(-641234)), (TwosCompInt(100), TwosCompInt(128))], 
            input_length: bx!(,120)
        });
        assert_eq!(res, Token::CharacterClass(std::rc::Rc::new(cls)));
    }

    #[test]
    fn ascii_char_class() {
        let input = "abc".chars().collect();
        let res = parse_char_class(&input);
        let mut options = HashSet::new();
        options.insert(UInt(97));
        options.insert(UInt(98));
        options.insert(UInt(99));
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: false, 
            endian: Endian::Big, 
            options, 
            ranges: vec![], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Ok(Token::CharacterClass(std::rc::Rc::new(cls))));

        let input = "a8:^abc".chars().collect();
        let res = parse_char_class(&input);
        let mut options = HashSet::new();
        options.insert(UInt(97));
        options.insert(UInt(98));
        options.insert(UInt(99));
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Big, 
            options, 
            ranges: vec![], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Ok(Token::CharacterClass(std::rc::Rc::new(cls))));

        let input = "\\\\a\\bc".chars().collect();
        let res = parse_char_class(&input);
        let mut options = HashSet::new();
        options.insert(UInt(92));
        options.insert(UInt(97));
        options.insert(UInt(98));
        options.insert(UInt(99));
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: false, 
            endian: Endian::Big, 
            options, 
            ranges: vec![], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Ok(Token::CharacterClass(std::rc::Rc::new(cls))));

        let input = "a8:abc0-9".chars().collect();
        let res = parse_char_class(&input);
        let mut options = HashSet::new();
        options.insert(UInt(97));
        options.insert(UInt(98));
        options.insert(UInt(99));
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: false, 
            endian: Endian::Big, 
            options, 
            ranges: vec![(UInt(48), UInt(57))], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Ok(Token::CharacterClass(std::rc::Rc::new(cls))));

        let input = "abc0-9\\--z".chars().collect();
        let res = parse_char_class(&input);
        let mut options = HashSet::new();
        options.insert(UInt(97));
        options.insert(UInt(98));
        options.insert(UInt(99));
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: false, 
            endian: Endian::Big, 
            options, 
            ranges: vec![(UInt(48), UInt(57)), (UInt(45), UInt(122))], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Ok(Token::CharacterClass(std::rc::Rc::new(cls))));

        let input = "a8:^0-9abc0-9d\\--zef".chars().collect();
        let res = parse_char_class(&input);
        let mut options = HashSet::new();
        options.insert(UInt(97));
        options.insert(UInt(98));
        options.insert(UInt(99));
        options.insert(UInt(100));
        options.insert(UInt(101));
        options.insert(UInt(102));
        let cls = DynamicCharacterClass::UInt(CharClass::<UInt>{
            inverted: true, 
            endian: Endian::Big, 
            options, 
            ranges: vec![(UInt(48), UInt(57)), (UInt(48), UInt(57)), (UInt(45), UInt(122))], 
            input_length: bx!(,8)
        });
        assert_eq!(res, Ok(Token::CharacterClass(std::rc::Rc::new(cls))));
    }

    #[test]
    fn group_headers() {
        let input = "___''..".chars().collect::<Vec<char>>();
        assert_eq!(parse_group_header(&input), Ok((GroupType::Numbered, 0)));
        let input = "?:___''..".chars().collect::<Vec<char>>();
        assert_eq!(parse_group_header(&input), Ok((GroupType::NonCapturing, 2)));
        let input = "?<hello>___''..".chars().collect::<Vec<char>>();
        assert_eq!(parse_group_header(&input), Ok((GroupType::Named("hello".to_string()), 8)));
    }

    #[test]
    fn groups_basic() {
        assert_eq!(BinRegex::new("_'.").unwrap().n_groups, 1);
        assert_eq!(BinRegex::new("(_'){5}_{2}").unwrap().n_groups, 2);
        assert_eq!(BinRegex::new("(_'){2,}_{2,}").unwrap().n_groups, 2);
        assert_eq!(BinRegex::new("(_'){2,4}_{1,10}").unwrap().n_groups, 2);
        assert_eq!(BinRegex::new("(_'){4,8}(_){1,2}").unwrap().n_groups, 3);
        assert_eq!(BinRegex::new("(_')+_+").unwrap().n_groups, 2);
        assert_eq!(BinRegex::new("((('')|(_'))*|_)*f0").unwrap().n_groups, 5);
    }
}