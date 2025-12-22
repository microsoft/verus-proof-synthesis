use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}


impl<C: SpecCombinator> SpecCombinator for &C {
    type Type = C::Type;

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (*self).spec_serialize(v)
    }

}


impl<C: SpecCombinator> SpecCombinator for Box<C> {
    type Type = C::Type;

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (**self).spec_serialize(v)
    }

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

    proof fn lemma_serialize_last_byte_high_8_bit_not_set(&self, v: UInt)
        ensures
            !is_high_8_bit_set!(self.spec_serialize(v).last()),
        decreases v,
    {
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        if hi == 0 {
            assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);
            assert(self.spec_serialize(v) == seq![lo]);
        } else {
            let s = Self::spec_serialize_helper(hi);
            assert(Self::spec_serialize_helper(v) == seq![set_high_8_bit!(lo)] + s);
            assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
            self.lemma_serialize_last_byte_high_8_bit_not_set(hi);
        }
    }

}




}
