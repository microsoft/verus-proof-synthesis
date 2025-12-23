use vstd::prelude::*;
use vstd::bytes::*;

fn main() {}

verus!{

// File: verus_extra/seq_lib_v.rs
	#[verifier::external_body]
pub proof fn lemma_fold_left_on_equiv_seqs<A, B>(s1: Seq<A>, s2: Seq<A>, eq: spec_fn(A, A) -> bool, init: B, f: spec_fn(B, A) -> B)
    requires
      s1.len() == s2.len(),
      (forall |i: int| 0 <= i < s1.len() ==> eq(s1[i], s2[i])),
      (forall |b: B, a1: A, a2: A| #[trigger] eq(a1, a2) ==> #[trigger] f(b, a1) == f(b, a2)),
    ensures
      s1.fold_left(init, f) == s2.fold_left(init, f)
    decreases s1.len(),
	{
		unimplemented!()
	}


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable()
  {unimplemented!()}

  spec fn view_equal(&self, other: &Self) -> bool;

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(&self, other: &Self)
    requires
      self.view_equal(other),
    ensures
      self.is_marshalable() == other.is_marshalable(),
      self.ghost_serialize() == other.ghost_serialize()
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
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
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
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
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

	#[verifier::external_body]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
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

  #[verifier::spinoff_prover]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
    // req, ens from trait
  {
    lemma_auto_spec_u64_to_from_le_bytes();
    assert(self@.len() == other@.len());
    assert forall |i: int| 0 <= i < self@.len() implies
      #[trigger] self@[i].is_marshalable() == other@[i].is_marshalable() &&
      #[trigger] self@[i].ghost_serialize() == other@[i].ghost_serialize() by {
        self@[i].lemma_same_views_serialize_the_same(&other@[i]);
    }
    let veq = |x: T, y: T| x.view_equal(&y);
    assert(self.is_marshalable() == other.is_marshalable()) by {
      assert((self@.len() <= usize::MAX) == (other@.len() <= usize::MAX));
      if (forall |x: T| self@.contains(x) ==> #[trigger] x.is_marshalable()) {
        assert forall |y: T| other@.contains(y) implies #[trigger] y.is_marshalable() by {
          let i = choose |i:int| 0 <= i < other@.len() && other@[i] == y;
          self@[i].lemma_same_views_serialize_the_same(&other@[i]);
        }
      } else {
        let i = choose |i:int| 0 <= i < self@.len() && !(#[trigger] self@[i].is_marshalable());
        self@[i].lemma_same_views_serialize_the_same(&other@[i]);
      }
      assert((self@.len() as usize).ghost_serialize().len() ==
             (other@.len() as usize).ghost_serialize().len());
      let f = |acc: int, x: T| acc + x.ghost_serialize().len();
      assert forall |b: int, a1: T, a2: T| #[trigger] veq(a1, a2) implies #[trigger] f(b, a1) == f(b, a2) by {
        a1.lemma_same_views_serialize_the_same(&a2);
      }
      lemma_fold_left_on_equiv_seqs(self@, other@, veq, 0, f);
      assert(self@.fold_left(0, f) == other@.fold_left(0, f));
    };
    assert(self.ghost_serialize() == other.ghost_serialize()) by {
      let f = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
      assert forall |b: Seq<u8>, a1: T, a2: T| #[trigger] veq(a1, a2) implies #[trigger] f(b, a1) == f(b, a2) by {
        a1.lemma_same_views_serialize_the_same(&a2);
      }
      lemma_fold_left_on_equiv_seqs(self@, other@, veq, Seq::<u8>::empty(), f);
    }
  }

}



}
