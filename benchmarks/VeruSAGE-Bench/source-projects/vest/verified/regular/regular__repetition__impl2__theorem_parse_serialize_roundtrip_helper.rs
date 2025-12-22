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

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.spec_parse(buf) matches Some((n, v)) ==> {
                &&& self.wf(v)
                &&& self.spec_serialize(v) == buf.take(n)
            },
            ;

    spec fn is_prefix_secure() -> bool;

    proof fn lemma_parse_length(&self, s: Seq<u8>)
        requires
            self.requires(),
        ensures
            self.spec_parse(s) matches Some((n, _)) ==> 0 <= n <= s.len(),
            ;

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

    open spec fn wf(&self, vs: Self::Type) -> bool {
        &&& vs.len() == self.1
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.0.wf(vs[i])
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.spec_parse_helper(s, self.1)
    }

    open spec fn spec_serialize(&self, vs: Self::Type) -> Seq<u8> {
        vs.fold_left(Seq::empty(), |acc: Seq<u8>, v| acc + self.0.spec_serialize(v))
    }

}


impl<C: SecureSpecCombinator> SecureSpecCombinator for RepeatN<C> {

    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

	#[verifier::external_body]
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
		unimplemented!()
	}


	#[verifier::external_body]
    proof fn lemma_parse_length(&self, s: Seq<u8>) {
		unimplemented!()
	}
}

impl<C: SecureSpecCombinator> RepeatN<C> {

    spec fn wf_helper(&self, vs: Seq<C::Type>, n: usize) -> bool {
        &&& vs.len() == n
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.0.wf(vs[i])
    }


	#[verifier::external_body]
    proof fn lemma_parse_length_helper(&self, s: Seq<u8>, n: usize)
        requires
            self.requires(),
        ensures
            self.spec_parse_helper(s, n) matches Some((m, _)) ==> 0 <= m <= s.len(),
        decreases n,
	{
		unimplemented!()
	}

    proof fn theorem_parse_serialize_roundtrip_helper(&self, buf: Seq<u8>, n: usize)
        requires
            self.requires(),
        ensures
            self.spec_parse_helper(buf, n) matches Some((m, vs)) ==> {
                &&& self.wf_helper(vs, n)
                &&& self.spec_serialize(vs) == buf.take(m)
            },
        decreases n,
    {
        if n == 0 {
            assert(buf.take(0) == Seq::<u8>::empty());
        } else {
            self.lemma_parse_length_helper(buf, n);  // <-- key
            self.lemma_parse_length_helper(buf, (n - 1) as usize);  // <-- key
            self.theorem_parse_serialize_roundtrip_helper(buf, (n - 1) as usize);  // <-- I.H.
            if let Some((m, vs)) = self.spec_parse_helper(buf, (n - 1) as usize) {
                self.0.lemma_parse_length(buf.skip(m as int));  // <-- key
                if let Some((k, v)) = self.0.spec_parse(buf.skip(m as int)) {
                    assert(vs.push(v).drop_last() == vs);
                    self.0.theorem_parse_serialize_roundtrip(buf.skip(m as int));  // <-- Base
                    assert(vs.push(v).last() == v);
                    assert(buf.take(m + k) == buf.take(m) + buf.skip(m).take(k));
                }
            }
        }
    }

}

}
