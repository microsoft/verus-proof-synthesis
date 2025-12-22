use vstd::prelude::*;

fn main() {}

verus!{


// File: src/properties.rs
/// Specification for parser and serializer [`Combinator`]s. All Vest combinators must implement this
/// trait.
pub trait SpecCombinator {
    /// The view of [`Combinator::Result`].
    type Type;

    /// The specification of [`Combinator::serialize`].
    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}


// File: src/regular/leb128.rs

/// Unsigned LEB128
pub struct UnsignedLEB128;

/// Result of UnsignedLEB128
pub type UInt = u64;

impl View for UnsignedLEB128 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        Self
    }

}

/// Take the lowest 7 bits as an u8
#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}

/// Set the highest bit to 1 as an u8
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
    /// Helper function for spec_serialize
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
    }

}
}
