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

    /// One of the top-level roundtrip properties
    /// It reads "if we successfully parse a byte sequence, then serializing the parsed value should
    /// give us the same byte sequence back."
    /// If we somehow get a different byte sequence, it means that different low-level representations
    /// can correspond to the same high-level value, or put differently, the same value can be
    /// serialized into different byte sequences.
    ///
    /// This property can be understood as
    /// 1. injectivity of parsing: different byte sequences should parse to different values (can
    ///    lead to parser mallability attacks if not satisfied)
    /// 2. correctness of serialization: given a correct parser that produces some value from a byte
    ///   sequence, the corresponding serializer should be able to serialize the value back to the same
    ///   byte sequence (up to the number of bytes consumed).
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.spec_parse(buf) matches Some((n, v)) ==> {
                &&& self.wf(v)
                &&& self.spec_serialize(v) == buf.take(n)
            },
    ;

    /// Like an associated constant, denotes whether the combinator is prefix-secure.
    spec fn is_prefix_secure() -> bool;

    /// This prefix-secure lemma is used in the proof of the roundtrip properties for sequencing
    /// and repeating combinators.
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        requires
            self.requires(),
        ensures
            Self::is_prefix_secure() ==> self.spec_parse(s1) is Some ==> self.spec_parse(s1 + s2)
                == self.spec_parse(s1),
    ;

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

// File: src/regular/repetition.rs
/// Combinator that repeats [C] combinator [self.1] times.
pub struct RepeatN<C>(pub C, pub usize);

impl<C: View> View for RepeatN<C> {
    type V = RepeatN<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        RepeatN(self.0@, self.1)
    }

}


impl<C: SecureSpecCombinator> RepeatN<C> {

    pub closed spec fn spec_parse_helper(&self, s: Seq<u8>, n: usize) -> Option<(int, Seq<C::Type>)>
        decreases n,
    {
        if n == 0 {
            Some((0, seq![]))
        } else {
            match self.spec_parse_helper(s, (n - 1) as usize) {
                Some((m, vs)) => match self.0.spec_parse(s.skip(m as int)) {
                    Some((k, v)) => Some((m + k, vs.push(v))),
                    None => None,
                },
                None => None,
            }
        }
    }

}



impl<C: SecureSpecCombinator> SpecCombinator for RepeatN<C> {
    type Type = Seq<C::Type>;

    open spec fn requires(&self) -> bool {
        &&& self.0.requires()
        &&& C::is_prefix_secure()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.spec_parse_helper(s, self.1)
    }

    #[verifier::external_body]
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {unimplemented!()}

}


impl<C: SecureSpecCombinator> SecureSpecCombinator for RepeatN<C> {

    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

    #[verifier::external_body]
    spec fn is_productive(&self) -> bool{
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    {unimplemented!()}

    #[verifier::external_body]
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {unimplemented!()}

    
    #[verifier::external_body]
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {unimplemented!()}

    #[verifier::external_body]
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    {unimplemented!()}


    #[verifier::external_body]
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    {unimplemented!()}


}

impl<C: SecureSpecCombinator> RepeatN<C> {

    proof fn lemma_prefix_secure_helper(&self, s1: Seq<u8>, s2: Seq<u8>, n: usize)
        requires
            self.requires(),
        ensures
            self.spec_parse_helper(s1, n) is Some ==> self.spec_parse_helper(s1.add(s2), n)
                == self.spec_parse_helper(s1, n),
    {
    }
}

}
