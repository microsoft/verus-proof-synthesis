use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

}

pub trait SecureSpecCombinator: SpecCombinator {}

// File: src/regular/leb128.rs
pub struct UnsignedLEB128;

pub type UInt = u64;

impl View for UnsignedLEB128 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        Self
    }

}

#[allow(unused_macros)]
macro_rules! uint_size { () => { 8 } }

#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => { $v as u8 >= 0x80 };
}

#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}

#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}

#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
}


impl SpecCombinator for UnsignedLEB128 {
    type Type = UInt;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
        decreases s.len(),
    {
        let v = take_low_7_bits!(s.first());

        if s.len() != 0 {
            if is_high_8_bit_set!(s.first()) {
                match self.spec_parse(s.drop_first()) {
                    Some(
                        (n, v2),
                    ) =>
                    // Check for overflow and canonicity (v2 should not be 0)
                    if n < usize::MAX && 0 < v2 <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                        Some((n + 1, v2 << 7 | v as Self::Type))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                Some((1, v as Self::Type))
            }
        } else {
            None
        }
    }

}


impl UnsignedLEB128 {

    proof fn lemma_spec_parse_low_7_bits(&self, s: Seq<u8>)
        requires
            s.len() != 0,
        ensures
            self.spec_parse(s) matches Some((_, x)) ==> {
                let s0 = s[0];
                take_low_7_bits!(x) == take_low_7_bits!(s0)
            },
    {
        let s0 = s[0];
        if is_high_8_bit_set!(s0) {
            if let Some((_, rest)) = self.spec_parse(s.drop_first()) {
                assert(take_low_7_bits!(rest << 7 | take_low_7_bits!(s0) as UInt)
                    == take_low_7_bits!(s0)) by (bit_vector);
            }
        } else {
            assert(take_low_7_bits!(take_low_7_bits!(s0)) == take_low_7_bits!(s0)) by (bit_vector);
        }
    }

}

}
