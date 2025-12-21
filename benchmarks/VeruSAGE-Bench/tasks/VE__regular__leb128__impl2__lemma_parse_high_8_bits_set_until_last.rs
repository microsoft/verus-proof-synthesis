use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
/// Specification for parser and serializer [`Combinator`]s. All Vest combinators must implement this
/// trait.
pub trait SpecCombinator {
    /// The view of [`Combinator::Result`].
    type Type;

    /// Pre-conditions for parsing and serialization.
    ///
    /// ## Examples
    ///
    /// - Sequencing combinators require that the first combinator is prefix-secure.
    /// - Repetition combinators require that the inner combinator is prefix-secure.
    /// - [`crate::regular::repetition::Repeat`] combinator requires that the
    ///   inner combinator is productive.
    /// - [`crate::regular::variant::Choice`] combinator requires that `Snd` is [`crate::regular::disjoint::DisjointFrom`] `Fst`.
    open spec fn requires(&self) -> bool {
        true
    }

    /// The specification of [`Combinator::parse`].
    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

}

/// Theorems and lemmas that must be proven for a combinator to be considered correct and secure.

pub trait SecureSpecCombinator: SpecCombinator {

    spec fn is_prefix_secure() -> bool;

    /// The parser-length lemma is used in the proof of the roundtrip properties and the prefix-secure
    /// lemma
    proof fn lemma_parse_length(&self, s: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.spec_parse(s) matches Some((n, _)) ==> 0 <= n <= s.len(),
            ;

    /// Like an associated constant, denotes whether the combinator is productive
    spec fn is_productive(&self) -> bool;

    /// This lemma is used in the proof of the roundtrip properties for optional and unbounded
    /// repeating combinators.
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.is_productive() ==> (self.spec_parse(s) matches Some((n, _)) ==> n > 0),
            ;
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

//pub(super) use uint_size;

/// Check if the highest bit is set in an u8
#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => { $v as u8 >= 0x80 };
}

//pub(crate) use is_high_8_bit_set;

/// Take the lowest 7 bits as an u8
#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}

//pub(crate) use take_low_7_bits;

/// Set the highest bit to 1 as an u8
#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}

//pub(super) use set_high_8_bit;

/// Max value for an n-bit unsigned integer
#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
}

//pub(super) use n_bit_max_unsigned;

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

impl SecureSpecCombinator for UnsignedLEB128 {

    open spec fn is_prefix_secure() -> bool {
        true
    }

    open spec fn is_productive(&self) -> bool {
        true
    }

    #[verifier::external_body]
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    {
        unimplemented!()
    }

}

impl UnsignedLEB128 {

    proof fn lemma_parse_high_8_bits_set_until_last(&self, s: Seq<u8>)
        ensures
            self.spec_parse(s) matches Some((n, v)) ==> {
                &&& forall|i: int| 0 <= i < n - 1 ==> is_high_8_bit_set!(s.spec_index(i))
            },
    {
    }

}


}
