use vstd::prelude::*;

fn main() {}

verus!{


// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}

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
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}

#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}

impl SpecCombinator for UnsignedLEB128 {
    type Type = UInt;

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        Self::spec_serialize_helper(v)
    }

}


impl UnsignedLEB128 {

    pub open spec fn spec_serialize_helper(v: UInt) -> Seq<u8>
        decreases v,
        via Self::spec_serialize_decreases
    {
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        if hi == 0 {
            seq![lo]
        } else {
            seq![set_high_8_bit!(lo)] + Self::spec_serialize_helper(hi)
        }
    }

    #[via_fn]
    proof fn spec_serialize_decreases(v: UInt) {
        assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
    }

    proof fn lemma_spec_serialize_length(&self, v: UInt)
        ensures
            self.spec_serialize(v).len() <= 10,
    {
        reveal_with_fuel(UnsignedLEB128::spec_serialize_helper, 10);
        assert(v >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 == 0) by (bit_vector);
    }

}




}
