use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
/// Specification for parser and serializer [`Combinator`]s. All Vest combinators must implement this
/// trait.
pub trait SpecCombinator {
    /// The view of [`Combinator::Result`].
    type Type;

    /// The specification of [`Combinator::parse`].
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

/// Byte size of UInt
#[allow(unused_macros)]
macro_rules! uint_size { () => { 8 } }

/// Check if the highest bit is set in an u8
#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => { $v as u8 >= 0x80 };
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

/// Max value for an n-bit unsigned integer
#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
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
    {
    }

}
}
