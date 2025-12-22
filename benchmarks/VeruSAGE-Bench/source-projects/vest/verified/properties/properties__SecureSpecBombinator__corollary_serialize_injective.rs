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

    proof fn corollary_serialize_injective(&self, v1: Self::Type, v2: Self::Type)
        requires
            self.requires(),
        ensures
            self.wf(v1) && self.wf(v2) ==> self.spec_serialize(v1) == self.spec_serialize(v2) ==> v1
                == v2,
    {
        self.theorem_serialize_parse_roundtrip(v1);
        self.theorem_serialize_parse_roundtrip(v2);
    }

    spec fn is_prefix_secure() -> bool;

}


}
