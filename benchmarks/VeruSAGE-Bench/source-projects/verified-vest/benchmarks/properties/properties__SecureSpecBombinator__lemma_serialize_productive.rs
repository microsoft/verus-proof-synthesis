use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }

    open spec fn requires(&self) -> bool {
        true
    }

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}

pub trait SecureSpecCombinator: SpecCombinator {

	#[verifier::external_body]
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        requires
            self.requires(),
        ensures
            self.wf(v) ==> self.spec_parse(self.spec_serialize(v)) == Some(
                (self.spec_serialize(v).len() as int, v),
            ),
	{
		unimplemented!()
	}

    spec fn is_prefix_secure() -> bool;

    spec fn is_productive(&self) -> bool;

	#[verifier::external_body]
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.is_productive() ==> (self.spec_parse(s) matches Some((n, _)) ==> n > 0),
	{
		unimplemented!()
	}

    proof fn lemma_serialize_productive(&self, v: Self::Type)
        requires
            self.requires(),
            self.wf(v),
        ensures
            self.is_productive() ==> self.spec_serialize(v).len() > 0,
    {
        self.theorem_serialize_parse_roundtrip(v);
        self.lemma_parse_productive(self.spec_serialize(v));
    }

}




}
