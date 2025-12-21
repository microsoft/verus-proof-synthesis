use vstd::prelude::*;

fn main() {}

verus!{

// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    open spec fn requires(&self) -> bool {
        true
    }

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>;

}


pub trait SecureSpecCombinator: SpecCombinator {

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

}

// File: src/regular/repetition.rs
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

}


impl<C: SecureSpecCombinator> SecureSpecCombinator for RepeatN<C> {

    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        self.1 > 0 && self.0.is_productive()
    }

	#[verifier::external_body]
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
		unimplemented!()
	}


}

impl<C: SecureSpecCombinator> RepeatN<C> {

    proof fn lemma_parse_productive_helper(&self, s: Seq<u8>, n: usize)
        requires
            self.requires(),
            self.1 > 0,
            self.0.is_productive(),
        ensures
            n > 0 ==> (self.spec_parse_helper(s, n) matches Some((consumed, _)) ==> consumed > 0),
        decreases n,
    {
        if n == 0 {
        } else {
            self.lemma_parse_productive_helper(s, (n - 1) as usize);
            match self.spec_parse_helper(s, (n - 1) as usize) {
                Some((m, vs)) => {
                    self.0.lemma_parse_productive(s.skip(m as int));
                },
                None => {},
            }
        }
    }

}

}
