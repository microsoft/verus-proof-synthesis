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

    /// The specification of [`Combinator::serialize`].
    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;

}

/// Theorems and lemmas that must be proven for a combinator to be considered correct and secure.
pub trait SecureSpecCombinator: SpecCombinator {

    /// Like an associated constant, denotes whether the combinator is prefix-secure.
    spec fn is_prefix_secure() -> bool;

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

    spec fn wf_helper(&self, vs: Seq<C::Type>, n: usize) -> bool {
        &&& vs.len() == n
        &&& forall|i: int| 0 <= i < vs.len() ==> #[trigger] self.0.wf(vs[i])
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

    open spec fn spec_serialize(&self, vs: Self::Type) -> Seq<u8> {
        vs.fold_left(Seq::empty(), |acc: Seq<u8>, v| acc + self.0.spec_serialize(v))
    }

}


impl<C: SecureSpecCombinator> SecureSpecCombinator for RepeatN<C> {

    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

}


impl<C: SecureSpecCombinator> RepeatN<C> {

    proof fn lemma_spec_serialize_max_length_2(&self, vs: Seq<C::Type>, n: usize)
        requires
            self.requires(),
            self.wf_helper(vs, n),
            self.spec_serialize(vs).len() <= usize::MAX,
        ensures
            forall|i: int|
                #![auto]
                0 <= i <= vs.len() ==> {
                    &&& self.spec_serialize(vs.take(i as int)).len() <= usize::MAX
                },
    {
    }

}

}
