mod bit_index;
pub use crate::bit_index::{BitIndex, BitIndexable};

mod bit_field;
pub use crate::bit_field::{BitField, BitPad};

mod semb;
pub use crate::semb::{Decimal, Semb};

pub mod bin_regex;
pub use crate::bin_regex::{BinRegex, BinMatch, BinCaptures};


#[cfg(test)]
mod match_tests {
    use crate::{BinRegex, BitField, BitIndex, bx};

    #[test]
    fn captures_basic() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        let re = BinRegex::new("(_'){4}_{2}").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,10)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101 00"));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,6), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("01"));

        let re = BinRegex::new("(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101"));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,6), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("01"));

        let re = BinRegex::new("_'((_')*)__('')(__'')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,16)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101 0011 0011"));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,2), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("0101 01"));
        assert_eq!(caps.get(2).unwrap().span(), (bx!(,6), bx!(,8)));
        assert_eq!(caps.get(2).unwrap().as_bf(), BitField::from_bin_str("01"));
        assert_eq!(caps.get(3).unwrap().span(), (bx!(,10), bx!(,12)));
        assert_eq!(caps.get(3).unwrap().as_bf(), BitField::from_bin_str("11"));
        assert_eq!(caps.get(4).unwrap().span(), (bx!(,12), bx!(,16)));
        assert_eq!(caps.get(4).unwrap().as_bf(), BitField::from_bin_str("0011"));

        let re = BinRegex::new("_'(?<foo>(?<bar>_')*)__(?:'')(?<test>__'')*").unwrap();
        assert_eq!(re.n_groups, 4);
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,16)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101 0011 0011"));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,2), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("0101 01"));
        assert_eq!(caps.get(2).unwrap().span(), (bx!(,6), bx!(,8)));
        assert_eq!(caps.get(2).unwrap().as_bf(), BitField::from_bin_str("01"));
        assert_eq!(caps.get(3).unwrap().span(), (bx!(,12), bx!(,16)));
        assert_eq!(caps.get(3).unwrap().as_bf(), BitField::from_bin_str("0011"));
        assert_eq!(caps.name("foo").unwrap().span(), (bx!(,2), bx!(,8)));
        assert_eq!(caps.name("foo").unwrap().as_bf(), BitField::from_bin_str("0101 01"));
        assert_eq!(caps.name("bar").unwrap().span(), (bx!(,6), bx!(,8)));
        assert_eq!(caps.name("bar").unwrap().as_bf(), BitField::from_bin_str("01"));
        assert_eq!(caps.name("test").unwrap().span(), (bx!(,12), bx!(,16)));
        assert_eq!(caps.name("test").unwrap().as_bf(), BitField::from_bin_str("0011"));

        let v = vec![0b11010101, 0b00110100, 0b11010100, 0b11010101, 0b11110000];
        let re = BinRegex::new("((('')|(_'))*|_)*f0").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,40)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,24), bx!(,32)));
        assert_eq!(caps.get(2).unwrap().span(), (bx!(,30), bx!(,32)));
        assert_eq!(caps.get(3).unwrap().span(), (bx!(,24), bx!(,26)));
        assert_eq!(caps.get(4).unwrap().span(), (bx!(,30), bx!(,32)));
    }

    #[test]
    fn longest_match() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        let re = BinRegex::new("(_')*_|(__)").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,10)));

        let re = BinRegex::new("(_')*?").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
    }

    #[test]
    fn basic() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        assert_eq!(BinRegex::new("_'.").unwrap().match_length(&v), Some(bx!(,3)));
        assert_eq!(BinRegex::new("_''").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("_'_'_'").unwrap().match_length(&v), Some(bx!(,6)));
        assert_eq!(BinRegex::new(".'_!'__").unwrap().match_length(&v), Some(bx!(,14)));
        assert_eq!(BinRegex::new("!!!").unwrap().match_length(&v), Some(bx!(,24)));
        assert_eq!(BinRegex::new(".!!!").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("!!........").unwrap().match_length(&v), Some(bx!(,24)));
        assert_eq!(BinRegex::new("!!____''''").unwrap().match_length(&v), Some(bx!(,24)));
        assert_eq!(BinRegex::new("!!!.").unwrap().match_length(&v), None);

        assert_eq!(BinRegex::new("55").unwrap().match_length(&v), Some(bx!(,8)));
        assert_eq!(BinRegex::new("_aA").unwrap().match_length(&v), Some(bx!(,9)));
        assert_eq!(BinRegex::new("_aA6_''0f").unwrap().match_length(&v), Some(bx!(,24)));
        assert_eq!(BinRegex::new("!..c'8_F").unwrap().match_length(&v), Some(bx!(,24)));
    }

    #[test]
    fn star_repetition() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        assert_eq!(BinRegex::new("!_*").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("!!.*_'").unwrap().match_length(&v), Some(bx!(,21)));
    }

    #[test]
    fn exact_repetition() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("_'_'_'_'_{2}").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_'){4}_{2}").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_'){5}_{2}").unwrap().match_length(&v), None);
    }    

    #[test]
    fn anchors() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        assert_eq!(BinRegex::new(":5;5;33:0f:").unwrap().match_length(&v), Some(bx!(,24)));
        assert_eq!(BinRegex::new(":5:5;33:0f:").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new(".:").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("..;").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new(":").unwrap().match_length(&v), Some(bx!(,0)));
    }

    #[test]
    fn repetition() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("_''?_?").unwrap().match_length(&v), Some(bx!(,3)));
        assert_eq!(BinRegex::new("_''?'").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("_'_'_'_'_{2}").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_'){4}_{2}").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_'){5}_{2}").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("(_'){2,}_{2,}").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_'){5,}_{2}").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("(_'){1,}").unwrap().match_length(&v), Some(bx!(,8)));
        assert_eq!(BinRegex::new("(_'){2,4}_{1,10}").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_'){4,8}_{1,2}").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_'){2,3}").unwrap().match_length(&v), Some(bx!(,6)));
        assert_eq!(BinRegex::new("(_'){5,10}").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("(_')+_+").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_')+__+").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(_')+___+").unwrap().match_length(&v), None);
    }

    #[test]
    fn laziness() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        let re = BinRegex::new("(_')??(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1), None);

        let re = BinRegex::new("(_')?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,0), bx!(,2)));

        let re = BinRegex::new("(_')*?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1), None);

        let re = BinRegex::new("(_')*?__").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,10)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,6), bx!(,8)));

        let re = BinRegex::new("(_')*(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,6), bx!(,8)));

        let re = BinRegex::new("(_')+?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,0), bx!(,2)));

        let re = BinRegex::new("(_')+(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,6), bx!(,8)));

        let re = BinRegex::new("(_'){2,}?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,2), bx!(,4)));

        let re = BinRegex::new("(_'){2,}(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,6), bx!(,8)));

        let re = BinRegex::new("(_'){1,3}?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,0), bx!(,2)));

        let re = BinRegex::new("(_'){1,3}(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,4), bx!(,6)));

        let re = BinRegex::new("(_'){2}?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,2), bx!(,4)));

        let re = BinRegex::new("(_'){2}(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx!(,0), bx!(,8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx!(,2), bx!(,4)));
    }

    #[test]
    fn greedy_revert() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("(_')*_'").unwrap().match_length(&v), Some(bx!(,8)));
        assert_eq!(BinRegex::new(".*__").unwrap().match_length(&v), Some(bx!(,14)));
        assert_eq!(BinRegex::new("(_')*_'.*_'_").unwrap().match_length(&v), Some(bx!(,9)));
        assert_eq!(BinRegex::new(".*:").unwrap().match_length(&v), Some(bx!(,16)));
        assert_eq!(BinRegex::new(".*:.").unwrap().match_length(&v), Some(bx!(,9)));
        assert_eq!(BinRegex::new(".*:.;").unwrap().match_length(&v), None);
    }

    #[test]
    fn choice() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("_|'").unwrap().match_length(&v), Some(bx!(,1)));
        assert_eq!(BinRegex::new("5|6").unwrap().match_length(&v), Some(bx!(,4)));
        assert_eq!(BinRegex::new("_a|7").unwrap().match_length(&v), Some(bx!(,5)));
        assert_eq!(BinRegex::new("_'5|f_'_|'6|7").unwrap().match_length(&v), Some(bx!(,13)));
    }

    #[test]
    fn ascii_char_class() {
        let v = "hello world! What's up?".as_bytes().to_vec();
        assert_eq!(BinRegex::new("[a-z]*").unwrap().match_length(&v), Some(BitIndex::new(5, 0)));
        assert_eq!(BinRegex::new("[a-z ]*").unwrap().match_length(&v), Some(BitIndex::new(11, 0)));
    }

    #[test]
    fn uint_char_class() {
        let v = vec![0b01100101, 0b01001110, 0b10010011, 0b11111111, 0b01010010, 0b00010011, 0b00010011];
        assert_eq!(BinRegex::new("[>u3:0..3]+[u3:^0..3]").unwrap().match_length(&v), Some(BitIndex::new(1, 4)));
        assert_eq!(BinRegex::new("[u4:^0..2]*[>u4:0..2]+").unwrap().match_length(&v), Some(BitIndex::new(5, 4)));
        assert_eq!(BinRegex::new("[u12:2514]").unwrap().find(&v).unwrap().span(), (bx!(,9), bx!(,9+12)));
        assert_eq!(BinRegex::new("[>u20:1026313]").unwrap().find(&v).unwrap().span(), (bx!(3, 3), bx!(5, 7)));
        assert_eq!(BinRegex::new("[<u22:3538852]").unwrap().find(&v).unwrap().span(), (bx!(1, 6), bx!(4, 4)));
    }

    #[test]
    fn iint_char_class() {
        let v = vec![0b01100101, 0b01001110, 0b10010011, 0b11111111, 0b01010010, 0b00010011, 0b00010011];
        // assert_eq!(BinRegex::new("[>u3:0..3]+[u3:^0..3]").unwrap().match_length(&v), Some(BitIndex::new(1, 4)));
        // assert_eq!(BinRegex::new("[u4:^0..2]*[>u4:0..2]+").unwrap().match_length(&v), Some(BitIndex::new(5, 4)));
        // assert_eq!(BinRegex::new("[u12:2514]").unwrap().find(&v).unwrap().span(), (bx!(,9), bx!(,9+12)));
        // assert_eq!(BinRegex::new("[>u20:1026313]").unwrap().find(&v).unwrap().span(), (bx!(3, 3), bx!(5, 7)));
        assert_eq!(BinRegex::new("[<i8:-87]").unwrap().find(&v).unwrap().span(), (bx!(0, 5), bx!(1, 5)));
        assert_eq!(BinRegex::new("[<i16:12577]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[>i8:-87]").unwrap().find(&v).unwrap().span(), (bx!(0, 5), bx!(1, 5)));
        assert_eq!(BinRegex::new("[>i16:-2783]").unwrap().find(&v).unwrap().span(), (bx!(3, 4), bx!(5, 4)));
        assert_eq!(BinRegex::new("[>i16:8497]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[<i16:8693]").unwrap().find(&v).unwrap().span(), (bx!(3, 4), bx!(5, 4)));
    }

    #[test]
    fn oint_char_class() {
        let v = vec![0b01100101, 0b01001110, 0b10010011, 0b11111111, 0b01010010, 0b00010011, 0b00010011];
        // assert_eq!(BinRegex::new("[>u3:0..3]+[u3:^0..3]").unwrap().match_length(&v), Some(BitIndex::new(1, 4)));
        // assert_eq!(BinRegex::new("[u4:^0..2]*[>u4:0..2]+").unwrap().match_length(&v), Some(BitIndex::new(5, 4)));
        // assert_eq!(BinRegex::new("[u12:2514]").unwrap().find(&v).unwrap().span(), (bx!(,9), bx!(,9+12)));
        // assert_eq!(BinRegex::new("[>u20:1026313]").unwrap().find(&v).unwrap().span(), (bx!(3, 3), bx!(5, 7)));
        assert_eq!(BinRegex::new("[<o16:-108]").unwrap().find(&v).unwrap().span(), (bx!(2, 0), bx!(4, 0)));
        assert_eq!(BinRegex::new("[<o16:12577]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[<o5:-12]").unwrap().find(&v).unwrap().span(), (bx!(1, 1), bx!(1, 6)));
        assert_eq!(BinRegex::new("[>o5:-12]").unwrap().find(&v).unwrap().span(), (bx!(1, 1), bx!(1, 6)));
        assert_eq!(BinRegex::new("[>o16:-173]").unwrap().find(&v).unwrap().span(), (bx!(3, 0), bx!(5, 0)));
        assert_eq!(BinRegex::new("[>o16:8497]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[>o5:-12][o10:-4..0]").unwrap().find(&v).unwrap().span(), (bx!(2, 3), bx!(4, 2)));
    }

    #[test]
    fn sint_char_class() {
        let v = vec![0b01100101, 0b01001110, 0b10010011, 0b11111111, 0b01010010, 0b00010011, 0b00010011];
        assert_eq!(BinRegex::new("[<s6:-7]").unwrap().find(&v).unwrap().span(), (bx!(1, 1), bx!(1, 7)));
        assert_eq!(BinRegex::new("[<s16:-32659]").unwrap().find(&v).unwrap().span(), (bx!(2, 0), bx!(4, 0)));
        assert_eq!(BinRegex::new("[<s16:12577]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[>s6:-7]").unwrap().find(&v).unwrap().span(), (bx!(1, 1), bx!(1, 7)));
        assert_eq!(BinRegex::new("[>s16:8497]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[>s16:-5119]").unwrap().find(&v).unwrap().span(), (bx!(2, 0), bx!(4, 0)));
        assert_eq!(BinRegex::new("[>s6:-7][>s8:-150..-100]").unwrap().find(&v).unwrap().span(), (bx!(2, 3), bx!(4, 1)));
    }

    #[test]
    fn nint_char_class() {
        let v = vec![0b01100101, 0b01001110, 0b10010011, 0b11111111, 0b01010010, 0b00010011, 0b00010011];
        assert_eq!(BinRegex::new("[<n6:-29]").unwrap().find(&v).unwrap().span(), (bx!(1, 1), bx!(1, 7)));
        assert_eq!(BinRegex::new("[<n16:-28870]").unwrap().find(&v).unwrap().span(), (bx!(1, 0), bx!(3, 0)));
        assert_eq!(BinRegex::new("[<n16:-3871]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[>n6:-29]").unwrap().find(&v).unwrap().span(), (bx!(1, 1), bx!(1, 7)));
        assert_eq!(BinRegex::new("[>n16:-7951]").unwrap().find(&v).unwrap().span(), (bx!(4, 4), bx!(6, 4)));
        assert_eq!(BinRegex::new("[>n16:14735]").unwrap().find(&v).unwrap().span(), (bx!(1, 0), bx!(3, 0)));
        assert_eq!(BinRegex::new("[>n6:-29][>n8:-100..-70]").unwrap().find(&v).unwrap().span(), (bx!(2, 3), bx!(4, 1)));
    }

    #[test]
    fn f32_char_class() {
        let v = vec![0b01100101, 0b01001110, 0b10010011, 0b11111111, 0b01010010, 0b00010011, 0b00010011];
        assert_eq!(BinRegex::new("[>f32:-1.450390125482823e+25]").unwrap().find(&v).unwrap().span(), (bx!(1, 4), bx!(5, 4)));
        assert_eq!(BinRegex::new("[<f32:1.6618762643686762e-18]").unwrap().find(&v).unwrap().span(), (bx!(1, 4), bx!(5, 4)));
        assert_eq!(BinRegex::new("[>f32:1e-5..1]").unwrap().find(&v).unwrap().span(), (bx!(1, 2), bx!(5, 2)));
        assert_eq!(BinRegex::new("[>f32:-1e-26..0]").unwrap().find(&v).unwrap().span(), (bx!(2, 0), bx!(6, 0)));
        assert_eq!(BinRegex::new("[<f32:100..120]").unwrap().find(&v).unwrap().span(), (bx!(1, 5), bx!(5, 5)));
        assert_eq!(BinRegex::new("[<f32:-snan]").unwrap().find(&v).unwrap().span(), (bx!(0, 0), bx!(4, 0)));
    }

    #[test]
    fn advanced() {
        let v = vec![0b11010101, 0b00110100, 0b11010100, 0b11010101, 0b11110000];
        assert_eq!(BinRegex::new("''(_')*__").unwrap().match_length(&v), Some(bx!(,10)));
        assert_eq!(BinRegex::new("(''(_')*__)*").unwrap().match_length(&v), Some(bx!(,24)));
        assert_eq!(BinRegex::new(".*(_')*_'!!").unwrap().match_length(&v), Some(bx!(,38)));
        assert_eq!(BinRegex::new("((('')|(_'))*|_)*f0").unwrap().match_length(&v), Some(bx!(,40)));
        //assert_eq!(BinRegex::new("([([('')(_')])*_])*f0").unwrap().match_length(&v), Some(bx!(,40)));
        //assert_eq!(BinRegex::new("[[('')(_')]*_]*f0").unwrap().match_length(&v), Some(bx!(,40)));
    }

    #[test]
    fn find() {
        let v = vec![0b11010101, 0b00110100, 0b11010100, 0b11010101, 0b11110000];

        let re = BinRegex::new("__''_'__").unwrap();
        let m = re.find(&v).unwrap();
        assert_eq!(m.span(), (bx!(,8), bx!(,16)));
        assert_eq!(m.as_bf(), BitField::from_bin_str("00110100"));

        let re = BinRegex::new(".''(_'){3,}..").unwrap();
        let m = re.find(&v).unwrap();
        assert_eq!(m.span(), (bx!(,23), bx!(,34)));
        assert_eq!(m.as_bf(), BitField::from_bin_str("01101010111"));

        let s = "My IP Address is 192.168.0.1. What's yours?".as_bytes().to_vec();
        let re = BinRegex::new(":([0-9]{0,3}[.]){3}[0-9]{0,3}").unwrap();
        let m = re.find(&s).unwrap();
        assert_eq!(m.span(), (BitIndex::new(17, 0), BitIndex::new(28, 0)));
    }

    #[test]
    fn find_iter() {
        let v = vec![0x0f, 0x00, 0x01, 0x12, 0xf6, 0xc5, 0x01, 0x60];

        let re = BinRegex::new("''(_+')+").unwrap();
        let mut re_iter = re.find_iter(&v);
        let m1 = re_iter.next().unwrap();
        assert_eq!(m1.span(), (BitIndex::new(0, 6), BitIndex::new(4, 1)));
        assert_eq!(m1.as_bf(), BitField::from_bin_str("11 0000 0000 0000 0001 0001 0010 1"));

        let m2 = re_iter.next().unwrap();
        assert_eq!(m2.span(), (BitIndex::new(4, 2), BitIndex::new(4, 6)));
        assert_eq!(m2.as_bf(), BitField::from_bin_str("11 01"));

        let m3 = re_iter.next().unwrap();
        assert_eq!(m3.span(), (BitIndex::new(5, 0), BitIndex::new(7, 2)));
        assert_eq!(m3.as_bf(), BitField::from_bin_str("1100 0101 0000 0001 01"));

        let m4 = re_iter.next();
        assert_eq!(m4, None);
    }
}
