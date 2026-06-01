use vstd::bytes::*;
use vstd::prelude::*;
fn main() {}
verus! {

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;

    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable();

    spec fn view_equal(&self, other: &Self) -> bool;

    proof fn lemma_view_equal_symmetric(&self, other: &Self)
        ensures
            self.view_equal(other) == other.view_equal(self);

    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
        requires
            !self.view_equal(other),
            self.ghost_serialize().len() <= other.ghost_serialize().len(),
        ensures
            self.ghost_serialize() != other.ghost_serialize().subrange(
                0,
                self.ghost_serialize().len() as int,
            );

    proof fn lemma_same_views_serialize_the_same(&self, other: &Self)
        requires
            self.view_equal(other),
        ensures
            self.is_marshalable() == other.is_marshalable(),
            self.ghost_serialize() == other.ghost_serialize();
}

impl Marshalable for u64 {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    #[verifier::external_body]
    proof fn lemma_view_equal_symmetric(&self, other: &Self) {
        unimplemented!()
    }

    open spec fn is_marshalable(&self) -> bool {
        true
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        spec_u64_to_le_bytes(*self)
    }

    #[verifier::external_body]
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self) {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self) {
        unimplemented!()
    }
}

impl Marshalable for usize {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    #[verifier::external_body]
    proof fn lemma_view_equal_symmetric(&self, other: &Self) {
        unimplemented!()
    }

    open spec fn is_marshalable(&self) -> bool {
        &&& *self as int <= u64::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (*self as u64).ghost_serialize()
    }

    #[verifier::external_body]
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self) {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self) {
        unimplemented!()
    }
}

impl Marshalable for Vec<u8> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        self@ === other@
    }

    #[verifier::external_body]
    proof fn lemma_view_equal_symmetric(&self, other: &Self) {
        unimplemented!()
    }

    open spec fn is_marshalable(&self) -> bool {
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
    }

    #[verifier::external_body]
    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self) {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self) {
        unimplemented!()
    }
}

impl<T: Marshalable> Marshalable for Vec<T> {
    open spec fn view_equal(&self, other: &Self) -> bool {
        let s = self@;
        let o = other@;
        s.len() == o.len() && (forall|i: int|
            0 <= i < s.len() ==> #[trigger] s[i].view_equal(&o[i]))
    }

    #[verifier::external_body]
    proof fn lemma_view_equal_symmetric(&self, other: &Self) {
        unimplemented!()
    }

    open spec fn is_marshalable(&self) -> bool {
        &&& self@.len() <= usize::MAX
        &&& (forall|x: T| self@.contains(x) ==> #[trigger] x.is_marshalable())
        &&& (self@.len() as usize).ghost_serialize().len() + self@.fold_left(
            0,
            |acc: int, x: T| acc + x.ghost_serialize().len(),
        ) <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@.fold_left(
            Seq::<u8>::empty(),
            |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
        )
    }

    #[verifier::external_body]
    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self) {
        unimplemented!()
    }

    proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self) {
    }
}

} // verus!
