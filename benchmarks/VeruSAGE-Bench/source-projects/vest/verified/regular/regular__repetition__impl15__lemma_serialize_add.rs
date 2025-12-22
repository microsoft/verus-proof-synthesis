use vstd::prelude::*;

fn main() {}

verus!{


// File: src/properties.rs
pub trait SpecCombinator {
    type Type;

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}


pub trait SecureSpecCombinator : SpecCombinator {}

// File: src/regular/repetition.rs
pub struct RepeatN<C>(pub C, pub usize);

impl<C: View> View for RepeatN<C> {
    type V = RepeatN<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        RepeatN(self.0@, self.1)
    }

}


impl<C: SecureSpecCombinator> SpecCombinator for RepeatN<C> {
    type Type = Seq<C::Type>;

    open spec fn spec_serialize(&self, vs: Self::Type) -> Seq<u8> {
        vs.fold_left(Seq::empty(), |acc: Seq<u8>, v| acc + self.0.spec_serialize(v))
    }

}


pub struct Repeat<C>(pub C);

impl<C: View> View for Repeat<C> {
    type V = Repeat<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        Repeat(self.0@)
    }

}

impl<C: SecureSpecCombinator> SpecCombinator for Repeat<C> {
    type Type = Seq<C::Type>;

    open spec fn spec_serialize(&self, vs: Self::Type) -> Seq<u8> {
        RepeatN(self.0, vs.len() as usize).spec_serialize(vs)
    }

}


impl<C: SecureSpecCombinator> Repeat<C> {

    #[verusfmt::skip]
    #[verifier::spinoff_prover]
    proof fn lemma_serialize_add(&self, v: C::Type, vs: Seq<C::Type>)
        ensures
            self.spec_serialize(seq![v] + vs) == self.0.spec_serialize(v) + self.spec_serialize(vs)
        decreases vs.len(),
    {
        if vs.len() == 0 {
            assert(vs == Seq::<C::Type>::empty());
            assert(seq![v].drop_last() == Seq::<C::Type>::empty());
        } else {
            let vs_ = vs.drop_last();
            let v_ = vs.last();
            self.lemma_serialize_add(v, vs_);
             // (1) I.H.
            assert(self.spec_serialize(seq![v] + vs_) == self.0.spec_serialize(v) + self.spec_serialize(vs_));
             // (2) "expand" `fold_left`
            assert(self.spec_serialize(vs) == self.spec_serialize(vs_) + self.0.spec_serialize((v_)));
             // by (1) and (2)
            assert(self.spec_serialize(seq![v] + vs_) + self.0.spec_serialize((v_))
                == self.0.spec_serialize(v) + self.spec_serialize(vs));
            assert(seq![v] + vs == (seq![v] + vs_).push(v_));
            assert(self.spec_serialize((seq![v] + vs_).push(v_))
                == self.spec_serialize(seq![v] + vs_) + self.0.spec_serialize((v_)))
            by { assert((seq![v] + vs_).push(v_).drop_last() == seq![v] + vs_); }
        }
    }

}



}
