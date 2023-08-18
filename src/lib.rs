mod bit_index;
pub use crate::bit_index::{BitIndex, BitIndexable};

mod bit_field;
pub use crate::bit_field::BitField;

pub mod bin_regex;
pub use crate::bin_regex::{BinRegex, BinMatch, BinCaptures};





/// Helper function for initializing [`BitIndex`](crate::BitIndex)
pub fn bx(bits: usize) -> BitIndex {
    BitIndex::new(bits >> 3, bits & 0x07)
}

#[cfg(test)]
mod match_tests {
    use crate::{BinRegex, BitField, bx};

    #[test]
    fn captures_basic() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        let re = BinRegex::new("(_'){4}_{2}").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(10)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101 00"));
        assert_eq!(caps.get(1).unwrap().span(), (bx(6), bx(8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("01"));

        let re = BinRegex::new("(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101"));
        assert_eq!(caps.get(1).unwrap().span(), (bx(6), bx(8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("01"));

        let re = BinRegex::new("_'((_')*)__('')(__'')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(16)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101 0011 0011"));
        assert_eq!(caps.get(1).unwrap().span(), (bx(2), bx(8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("0101 01"));
        assert_eq!(caps.get(2).unwrap().span(), (bx(6), bx(8)));
        assert_eq!(caps.get(2).unwrap().as_bf(), BitField::from_bin_str("01"));
        assert_eq!(caps.get(3).unwrap().span(), (bx(10), bx(12)));
        assert_eq!(caps.get(3).unwrap().as_bf(), BitField::from_bin_str("11"));
        assert_eq!(caps.get(4).unwrap().span(), (bx(12), bx(16)));
        assert_eq!(caps.get(4).unwrap().as_bf(), BitField::from_bin_str("0011"));

        let re = BinRegex::new("_'(?<foo>(?<bar>_')*)__(?:'')(?<test>__'')*").unwrap();
        assert_eq!(re.n_groups, 4);
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(16)));
        assert_eq!(caps.get(0).unwrap().as_bf(), BitField::from_bin_str("0101 0101 0011 0011"));
        assert_eq!(caps.get(1).unwrap().span(), (bx(2), bx(8)));
        assert_eq!(caps.get(1).unwrap().as_bf(), BitField::from_bin_str("0101 01"));
        assert_eq!(caps.get(2).unwrap().span(), (bx(6), bx(8)));
        assert_eq!(caps.get(2).unwrap().as_bf(), BitField::from_bin_str("01"));
        assert_eq!(caps.get(3).unwrap().span(), (bx(12), bx(16)));
        assert_eq!(caps.get(3).unwrap().as_bf(), BitField::from_bin_str("0011"));
        assert_eq!(caps.name("foo").unwrap().span(), (bx(2), bx(8)));
        assert_eq!(caps.name("foo").unwrap().as_bf(), BitField::from_bin_str("0101 01"));
        assert_eq!(caps.name("bar").unwrap().span(), (bx(6), bx(8)));
        assert_eq!(caps.name("bar").unwrap().as_bf(), BitField::from_bin_str("01"));
        assert_eq!(caps.name("test").unwrap().span(), (bx(12), bx(16)));
        assert_eq!(caps.name("test").unwrap().as_bf(), BitField::from_bin_str("0011"));

        let v = vec![0b11010101, 0b00110100, 0b11010100, 0b11010101, 0b11110000];
        let re = BinRegex::new("((('')|(_'))*|_)*f0").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(40)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(24), bx(32)));
        assert_eq!(caps.get(2).unwrap().span(), (bx(30), bx(32)));
        assert_eq!(caps.get(3).unwrap().span(), (bx(24), bx(26)));
        assert_eq!(caps.get(4).unwrap().span(), (bx(30), bx(32)));
    }

    #[test]
    fn longest_match() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        let re = BinRegex::new("(_')*_|(__)").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(10)));

        let re = BinRegex::new("(_')*?").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
    }

    #[test]
    fn basic() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        assert_eq!(BinRegex::new("_'.").unwrap().match_length(&v), Some(bx(3)));
        assert_eq!(BinRegex::new("_''").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("_'_'_'").unwrap().match_length(&v), Some(bx(6)));
        assert_eq!(BinRegex::new(".'_!'__").unwrap().match_length(&v), Some(bx(14)));
        assert_eq!(BinRegex::new("!!!").unwrap().match_length(&v), Some(bx(24)));
        assert_eq!(BinRegex::new(".!!!").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("!!........").unwrap().match_length(&v), Some(bx(24)));
        assert_eq!(BinRegex::new("!!____''''").unwrap().match_length(&v), Some(bx(24)));
        assert_eq!(BinRegex::new("!!!.").unwrap().match_length(&v), None);

        assert_eq!(BinRegex::new("55").unwrap().match_length(&v), Some(bx(8)));
        assert_eq!(BinRegex::new("_aA").unwrap().match_length(&v), Some(bx(9)));
        assert_eq!(BinRegex::new("_aA6_''0f").unwrap().match_length(&v), Some(bx(24)));
        assert_eq!(BinRegex::new("!..c'8_F").unwrap().match_length(&v), Some(bx(24)));
    }

    #[test]
    fn star_repetition() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        assert_eq!(BinRegex::new("!_*").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("!!.*_'").unwrap().match_length(&v), Some(bx(21)));
    }

    #[test]
    fn exact_repetition() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("_'_'_'_'_{2}").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_'){4}_{2}").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_'){5}_{2}").unwrap().match_length(&v), None);
    }    

    #[test]
    fn anchors() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        assert_eq!(BinRegex::new(":5;5;33:0f:").unwrap().match_length(&v), Some(bx(24)));
        assert_eq!(BinRegex::new(":5:5;33:0f:").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new(".:").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("..;").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new(":").unwrap().match_length(&v), Some(bx(0)));
    }

    #[test]
    fn repetition() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("_''?_?").unwrap().match_length(&v), Some(bx(3)));
        assert_eq!(BinRegex::new("_''?'").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("_'_'_'_'_{2}").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_'){4}_{2}").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_'){5}_{2}").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("(_'){2,}_{2,}").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_'){5,}_{2}").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("(_'){1,}").unwrap().match_length(&v), Some(bx(8)));
        assert_eq!(BinRegex::new("(_'){2,4}_{1,10}").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_'){4,8}_{1,2}").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_'){2,3}").unwrap().match_length(&v), Some(bx(6)));
        assert_eq!(BinRegex::new("(_'){5,10}").unwrap().match_length(&v), None);
        assert_eq!(BinRegex::new("(_')+_+").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_')+__+").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(_')+___+").unwrap().match_length(&v), None);
    }

    #[test]
    fn laziness() {
        let v = vec![0b01010101, 0b00110011, 0b00001111];
        let re = BinRegex::new("(_')??(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1), None);

        let re = BinRegex::new("(_')?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(0), bx(2)));

        let re = BinRegex::new("(_')*?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1), None);

        let re = BinRegex::new("(_')*?__").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(10)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(6), bx(8)));

        let re = BinRegex::new("(_')*(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(6), bx(8)));

        let re = BinRegex::new("(_')+?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(0), bx(2)));

        let re = BinRegex::new("(_')+(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(6), bx(8)));

        let re = BinRegex::new("(_'){2,}?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(2), bx(4)));

        let re = BinRegex::new("(_'){2,}(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(6), bx(8)));

        let re = BinRegex::new("(_'){1,3}?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(0), bx(2)));

        let re = BinRegex::new("(_'){1,3}(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(4), bx(6)));

        let re = BinRegex::new("(_'){2}?(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(2), bx(4)));

        let re = BinRegex::new("(_'){2}(_')*").unwrap();
        let caps = re.captures(&v).unwrap();
        assert_eq!(caps.get(0).unwrap().span(), (bx(0), bx(8)));
        assert_eq!(caps.get(1).unwrap().span(), (bx(2), bx(4)));
    }

    #[test]
    fn greedy_revert() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("(_')*_'").unwrap().match_length(&v), Some(bx(8)));
        assert_eq!(BinRegex::new(".*__").unwrap().match_length(&v), Some(bx(14)));
        assert_eq!(BinRegex::new("(_')*_'.*_'_").unwrap().match_length(&v), Some(bx(9)));
        assert_eq!(BinRegex::new(".*:").unwrap().match_length(&v), Some(bx(16)));
        assert_eq!(BinRegex::new(".*:.").unwrap().match_length(&v), Some(bx(9)));
        assert_eq!(BinRegex::new(".*:.;").unwrap().match_length(&v), None);
    }

    #[test]
    fn choice() {
        let v = vec![0b01010101, 0b00110011];
        assert_eq!(BinRegex::new("_|'").unwrap().match_length(&v), Some(bx(1)));
        assert_eq!(BinRegex::new("5|6").unwrap().match_length(&v), Some(bx(4)));
        assert_eq!(BinRegex::new("_a|7").unwrap().match_length(&v), Some(bx(5)));
        assert_eq!(BinRegex::new("_'5|f_'_|'6|7").unwrap().match_length(&v), Some(bx(13)));
    }

    #[test]
    fn advanced() {
        let v = vec![0b11010101, 0b00110100, 0b11010100, 0b11010101, 0b11110000];
        assert_eq!(BinRegex::new("''(_')*__").unwrap().match_length(&v), Some(bx(10)));
        assert_eq!(BinRegex::new("(''(_')*__)*").unwrap().match_length(&v), Some(bx(24)));
        assert_eq!(BinRegex::new(".*(_')*_'!!").unwrap().match_length(&v), Some(bx(38)));
        assert_eq!(BinRegex::new("((('')|(_'))*|_)*f0").unwrap().match_length(&v), Some(bx(40)));
        //assert_eq!(BinRegex::new("([([('')(_')])*_])*f0").unwrap().match_length(&v), Some(bx(40)));
        //assert_eq!(BinRegex::new("[[('')(_')]*_]*f0").unwrap().match_length(&v), Some(bx(40)));
    }

    #[test]
    fn find() {
        let v = vec![0b11010101, 0b00110100, 0b11010100, 0b11010101, 0b11110000];

        let re = BinRegex::new("__''_'__").unwrap();
        let m = re.find(&v).unwrap();
        assert_eq!(m.span(), (bx(8), bx(16)));
        assert_eq!(m.as_bf(), BitField::from_bin_str("00110100"));

        let re = BinRegex::new(".''(_'){3,}..").unwrap();
        let m = re.find(&v).unwrap();
        assert_eq!(m.span(), (bx(23), bx(34)));
        assert_eq!(m.as_bf(), BitField::from_bin_str("01101010111"));
    }
}
