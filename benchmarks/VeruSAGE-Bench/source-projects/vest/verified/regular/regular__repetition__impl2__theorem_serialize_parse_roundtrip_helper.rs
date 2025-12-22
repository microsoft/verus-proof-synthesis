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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        requires
            self.requires(),
        ensures
            self.wf(v) ==> self.spec_parse(self.spec_serialize(v)) == Some(
                (self.spec_serialize(v).len() as int, v),
            ),
            ;

    spec fn is_prefix_secure() -> bool;

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
    proof fn theorem_serialize_parse_roundtrip(&self, vs: Self::Type) {
		unimplemented!()
	}

}

impl<C: SecureSpecCombinator> RepeatN<C> {

    spec fn wf_helper(&self, vs: Seq<C::Type>, n: usize) -> bool {
        &&& vs.len() == n
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.0.wf(vs[i])
    }

	#[verifier::external_body]
    proof fn lemma_prefix_secure_helper(&self, s1: Seq<u8>, s2: Seq<u8>, n: usize)
        requires
            self.requires(),
        ensures
            self.spec_parse_helper(s1, n) is Some ==> self.spec_parse_helper(s1.add(s2), n)
                == self.spec_parse_helper(s1, n),
        decreases n,
	{
		unimplemented!()
	}


    proof fn theorem_serialize_parse_roundtrip_helper(&self, vs: Seq<C::Type>, n: usize)
        requires
            self.requires(),
        ensures
            self.wf_helper(vs, n) ==> self.spec_parse_helper(self.spec_serialize(vs), n) == Some(
                (self.spec_serialize(vs).len() as int, vs),
            ),
        decreases vs.len(), n,
    {
        if self.wf_helper(vs, n) {
            if vs.len() == 0 {
                assert(self.spec_parse_helper(self.spec_serialize(vs), n) == Some(
                    (self.spec_serialize(vs).len() as int, vs),
                ));
            } else {
                assert(n != 0);
                let (v_, vs_) = (vs.last(), vs.drop_last());
                self.0.theorem_serialize_parse_roundtrip(v_);  // <-- Base
                self.theorem_serialize_parse_roundtrip_helper(vs_, (n - 1) as usize);  // <-- I.H.
                let buf0 = self.0.spec_serialize(v_);
                let buf1 = self.spec_serialize(vs_);
                let (n0, n1) = (buf0.len() as int, buf1.len() as int);
                assert(vs_.push(v_) == vs);  // <-- (1).
                assert(self.spec_serialize(vs) == buf1 + buf0);  // <-- from (0) and (1)
                assert(self.0.spec_parse(buf0) == Some((n0, v_)));  // <-- from Base
                assert(self.spec_parse_helper(buf1, (n - 1) as usize) == Some((n1, vs_)));  // <-- from I.H.
                self.lemma_prefix_secure_helper(buf1, buf0, (n - 1) as usize);
                assert((buf1 + buf0).skip(n1) == buf0);
                assert(self.spec_parse_helper(buf1 + buf0, n) == Some((n0 + n1, vs)));
            }
        }
    }

}

}
