use crate::bit_index::{BitIndex, BitIndexable};
use crate::bit_field::{BitField};

enum TextEncoding {
    Ascii,
    Utf8,
    Utf16,
    Hex
}

trait CharClass {
    fn length(&self) -> BitIndex,
    fn check(BitField) -> bool
}

struct AsciiRange {
    start: u8,
    end: u8
}

impl CharClass for AsciiRange {
    fn length(&self) -> BitIndex {BitIndex::new(0, 1)}
    fn check(&self, input: &BitField) {
        let x = input.extract_u8(BitIndex::new(0, 0));
        start <= x && x <= end
    }
}

// [utf8:a-zA-Z0] matches utf-8 characters a-z, A-Z, or 0.
