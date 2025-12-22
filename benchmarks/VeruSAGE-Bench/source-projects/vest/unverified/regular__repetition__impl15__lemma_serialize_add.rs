use vstd::prelude::*;

fn main() {}

verus!{


// File: src/properties.rs
/// Specification for parser and serializer [`Combinator`]s. All Vest combinators must implement this
/// trait.
pub trait SpecCombinator {
    /// The view of [`Combinator::Result`].
    type Type;

    /// The specification of [`Combinator::serialize`].
    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}

/// Theorems and lemmas that must be proven for a combinator to be considered correct and secure.
pub trait SecureSpecCombinator : SpecCombinator {}

// File: src/regular/repetition.rs
/// Combinator that repeats [C] combinator [self.1] times.
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

/// A combinator to repeatedly parse/serialize the inner combinator C
/// until the end of the buffer.
///
/// If the inner combinator fails before the end of the buffer, Repeat fails
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
    proof fn lemma_serialize_add(&self, v: C::Type, vs: Seq<C::Type>)
        ensures
            self.spec_serialize(seq![v] + vs) == self.0.spec_serialize(v) + self.spec_serialize(vs)
    {
    }

}



}
