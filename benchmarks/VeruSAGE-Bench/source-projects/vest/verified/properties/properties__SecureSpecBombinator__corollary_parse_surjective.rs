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

    spec fn is_prefix_secure() -> bool;

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

    proof fn corollary_parse_surjective(&self, v: Self::Type)
        requires
            self.requires(),
            self.wf(v),
        ensures
            exists|b: Seq<u8>| #[trigger] self.spec_parse(b) matches Some((_, v_)) && v_ == v,
    {
        self.theorem_serialize_parse_roundtrip(v);
    }


}

}
