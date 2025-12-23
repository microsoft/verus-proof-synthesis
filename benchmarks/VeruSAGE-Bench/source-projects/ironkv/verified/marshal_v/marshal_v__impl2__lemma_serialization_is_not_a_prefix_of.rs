use vstd::prelude::*;
use vstd::bytes::*;

fn main() {}

verus!{

// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable(),
  {unimplemented!()}

  spec fn view_equal(&self, other: &Self) -> bool;

	#[verifier::external_body]
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
    requires
      !self.view_equal(other),
      self.ghost_serialize().len() <= other.ghost_serialize().len(),
    ensures
      self.ghost_serialize() != other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int),
  {unimplemented!()}

}


impl Marshalable for u64 {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

  open spec fn is_marshalable(&self) -> bool {
    true
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    spec_u64_to_le_bytes(*self)
  }

	#[verifier::external_body]
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
	{
		unimplemented!()
	}

}


impl Marshalable for usize {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

  open spec fn is_marshalable(&self) -> bool {
    &&& *self as int <= u64::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (*self as u64).ghost_serialize()
  }

	#[verifier::external_body]
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
	{
		unimplemented!()
	}

}


impl Marshalable for Vec<u8> {

  open spec fn view_equal(&self, other: &Self) -> bool {
    self@ === other@
  }

  open spec fn is_marshalable(&self) -> bool {
    self@.len() <= usize::MAX &&
    (self@.len() as usize).ghost_serialize().len() + self@.len() as int <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@
  }

  #[verifier::spinoff_prover]
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
    // req, ens from trait
  {
    lemma_auto_spec_u64_to_from_le_bytes();
    assert(self.ghost_serialize().subrange(0, 8) =~= (self@.len() as usize).ghost_serialize());
    assert(other.ghost_serialize().subrange(0, 8) =~= (other@.len() as usize).ghost_serialize());
    if self.ghost_serialize().len() == other.ghost_serialize().len() {
      assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int) =~= other.ghost_serialize());
      assert(self.ghost_serialize().subrange(8, self.ghost_serialize().len() as int) =~= self@);
      assert(other.ghost_serialize().subrange(8, self.ghost_serialize().len() as int) =~= other@);
    } else {
      assert(other.len() > self.len()); // OBSERVE
      assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int).subrange(0, 8) =~= other.ghost_serialize().subrange(0, 8));
    }
  }

}


impl<T: Marshalable> Marshalable for Vec<T> {

  open spec fn view_equal(&self, other: &Self) -> bool {
    let s = self@;
    let o = other@;
    s.len() == o.len() && (forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i].view_equal(&o[i]))
  }

  open spec fn is_marshalable(&self) -> bool {
    &&& self@.len() <= usize::MAX
    &&& (forall |x: T| self@.contains(x) ==> #[trigger] x.is_marshalable())
    &&& (self@.len() as usize).ghost_serialize().len() +
        self@.fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()) <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@.fold_left(Seq::<u8>::empty(), |acc: Seq<u8>, x: T| acc + x.ghost_serialize())
  }

	#[verifier::external_body]
  #[verifier::spinoff_prover]
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
	{
		unimplemented!()
	}

}



}
