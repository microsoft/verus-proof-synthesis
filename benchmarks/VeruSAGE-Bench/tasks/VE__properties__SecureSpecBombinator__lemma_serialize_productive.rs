use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
/// Specification for parser and serializer [`Combinator`]s. All Vest combinators must implement this
/// trait.
pub trait SpecCombinator {
    /// The view of [`Combinator::Result`].
    type Type;

    /// Well-formedness of the format [`Self::type`] (e.g., refinements on the type).
    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }

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

    /// The specification of [`Combinator::serialize`].
    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}

/// Theorems and lemmas that must be proven for a combinator to be considered correct and secure.
pub trait SecureSpecCombinator: SpecCombinator {

    spec fn is_prefix_secure() -> bool;

    spec fn is_productive(&self) -> bool;

    /// One of the top-level roundtrip properties
    /// It reads "if we serialize a (well-formed) value, then parsing the serialized bytes should
    /// give us the same value back."
    /// If we somehow get a different value, it means that different high-level values can
    /// correspond to the same low-level representation, or put differently, the same byte
    /// sequences can be parsed into different values.
    ///
    /// This property can be understood as
    /// 1. injectivity of serialization: different values should serialize to different byte
    ///    sequences
    /// 2. surjectivity of parsing: every valid high-level value should associate with at least one
    ///    low-level representation.
    /// 3. correctness of parsing: given a correct serializer that produces some byte sequence from
    ///   a value, the corresponding parser should be able to parse the byte sequence back to the
    ///   same value (can lead to format-confusion attacks if not satisfied).
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        requires
            self.requires(),
        ensures
            self.wf(v) ==> self.spec_parse(self.spec_serialize(v)) == Some(
                (self.spec_serialize(v).len() as int, v),
            ),
            ;

    /// This lemma is used in the proof of the roundtrip properties for optional and unbounded
    /// repeating combinators.
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.is_productive() ==> (self.spec_parse(s) matches Some((n, _)) ==> n > 0),
            ;

    /// This lemma is used in the proof of the roundtrip properties for optional and unbounded
    /// repeating combinators.
    proof fn lemma_serialize_productive(&self, v: Self::Type)
        requires
            self.requires(),
            self.wf(v),
        ensures
            self.is_productive() ==> self.spec_serialize(v).len() > 0,
    {
    }

}
}
