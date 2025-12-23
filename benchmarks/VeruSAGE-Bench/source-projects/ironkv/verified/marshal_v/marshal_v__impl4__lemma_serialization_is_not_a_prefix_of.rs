use vstd::prelude::*;
use vstd::bytes::*;

fn main() {}

verus!{

// File: verus_extra/choose_v.rs
	#[verifier::external_body]
pub proof fn choose_smallest(low: int, high: int, p: spec_fn(int)->bool) -> (res:int)
  requires
    exists |i:int| #![trigger(p(i))] low <= i < high && p(i),
  ensures
    low <= res < high,
    p(res),
    forall |i:int| #![trigger(p(i))] low <= i < res ==> !p(i),
  decreases
    high - low,
	{
		unimplemented!()
	}


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

	#[verifier::external_body]
pub proof fn lemma_fold_left_append_merge<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> Seq<B>)
  ensures
    (s1 + s2).fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
      ==
    s1.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
      +
    s2.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
  decreases
    s1.len() + s2.len()
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn some_differing_index_for_unequal_seqs<A>(s1: Seq<A>, s2: Seq<A>) -> (i: int)
  requires
    s1 != s2,
    s1.len() == s2.len(),
  ensures
    0 <= i < s1.len(),
    s1[i] != s2[i],
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
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
    ensures self.view_equal(other) == other.view_equal(self)
  {unimplemented!()}

	#[verifier::external_body]
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
    requires
      !self.view_equal(other),
      self.ghost_serialize().len() <= other.ghost_serialize().len(),
    ensures
      self.ghost_serialize() != other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)
  {unimplemented!()}

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

	#[verifier::external_body]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
	{
		unimplemented!()
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

	#[verifier::external_body]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
	{
		unimplemented!()
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

	#[verifier::external_body]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
	{
		unimplemented!()
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
  #[verifier::spinoff_prover]
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
	{
		unimplemented!()
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

	#[verifier::external_body]
  #[verifier::spinoff_prover]
  proof fn lemma_view_equal_symmetric(&self, other: &Self)
	{
		unimplemented!()
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
  proof fn lemma_serialization_is_not_a_prefix_of(&self, other: &Self)
    // req, ens from trait
  {
    lemma_auto_spec_u64_to_from_le_bytes();
    if self.len() != other.len() {
      assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int).subrange(0, 8) =~= other.ghost_serialize().subrange(0, 8));
      assert(self.ghost_serialize().subrange(0, 8) =~= (self.len() as usize).ghost_serialize());
      assert(other.ghost_serialize().subrange(0, 8) =~= (other.len() as usize).ghost_serialize());
    } else {
      let not_view_equal_at_idx = |i:int| !self@[i].view_equal(&other@[i]);
      let idx = {
        let temp = choose |i:int| 0 <= i < self@.len() && !#[trigger] self@[i].view_equal(&other@[i]);
        assert (not_view_equal_at_idx(temp)); // OBSERVE
        choose_smallest(0, self@.len() as int, not_view_equal_at_idx)
      };
      let emp = Seq::<u8>::empty();
      let g = |x: T| x.ghost_serialize();
      let accg = |acc: Seq<u8>, x: T| acc + g(x);
      let accgs = |acc: Seq<u8>, x: T| acc + x.ghost_serialize();
      let gs = |s: Seq<T>, start: int, end: int| s.subrange(start, end).fold_left(emp, accg);
      assert(accg =~= accgs);
      assert(self.ghost_serialize() =~= ((self@.len() as usize).ghost_serialize() + gs(self@, 0, idx)) + g(self@[idx]) + gs(self@, idx + 1, self.len() as int)) by {
        assert(gs(self@, 0, self.len() as int) == gs(self@, 0, idx) + gs(self@, idx, self.len() as int)) by {
          let s1 = self@.subrange(0, idx);
          let s2 = self@.subrange(idx, self.len() as int);
          lemma_fold_left_append_merge(s1, s2, g);
          assert(self@.subrange(0, self.len() as int) =~= s1 + s2);
        }
        assert(gs(self@, idx, self.len() as int) == g(self@[idx]) + gs(self@, idx + 1, self.len() as int)) by {
          let s1 = self@.subrange(idx, idx + 1);
          let s2 = self@.subrange(idx + 1, self.len() as int);
          lemma_fold_left_append_merge(s1, s2, g);
          assert(self@.subrange(idx, self.len() as int) =~= s1 + s2);
          assert(self@.subrange(idx, idx + 1) =~= seq![self@[idx]]);
          reveal_with_fuel(Seq::fold_left, 2);
          assert(emp + g(self@[idx]) =~= g(self@[idx]));
        }
        assert((self@.len() as usize).ghost_serialize() + gs(self@, 0, self.len() as int) == self.ghost_serialize()) by {
          assert(self@.subrange(0, self.len() as int) =~= self@);
        }
      }
      assert(other.ghost_serialize() =~= ((other@.len() as usize).ghost_serialize() + gs(other@, 0, idx)) + g(other@[idx]) + gs(other@, idx + 1, other.len() as int)) by {
        assert(gs(other@, 0, other.len() as int) == gs(other@, 0, idx) + gs(other@, idx, other.len() as int)) by {
          let s1 = other@.subrange(0, idx);
          let s2 = other@.subrange(idx, other.len() as int);
          lemma_fold_left_append_merge(s1, s2, g);
          assert(other@.subrange(0, other.len() as int) =~= s1 + s2);
        }
        assert(gs(other@, idx, other.len() as int) == g(other@[idx]) + gs(other@, idx + 1, other.len() as int)) by {
          let s1 = other@.subrange(idx, idx + 1);
          let s2 = other@.subrange(idx + 1, other.len() as int);
          lemma_fold_left_append_merge(s1, s2, g);
          assert(other@.subrange(idx, other.len() as int) =~= s1 + s2);
          assert(other@.subrange(idx, idx + 1) =~= seq![other@[idx]]);
          reveal_with_fuel(Seq::fold_left, 2);
          assert(emp + g(other@[idx]) =~= g(other@[idx]));
        }
        assert((other@.len() as usize).ghost_serialize() + gs(other@, 0, other.len() as int) == other.ghost_serialize()) by {
          assert(other@.subrange(0, other.len() as int) =~= other@);
        }
      }
      assert((self@.len() as usize).ghost_serialize() == (other@.len() as usize).ghost_serialize());
      assert(gs(self@, 0, idx) == gs(other@, 0, idx)) by {
        assert forall |i:int| 0 <= i < idx implies g(self@.subrange(0, idx)[i]) == g(other@.subrange(0, idx)[i]) by {
          assert(self@.subrange(0, idx)[i] == self@[i] && other@.subrange(0, idx)[i] == other@[i]);
          assert(!not_view_equal_at_idx(i));
          self@[i].lemma_same_views_serialize_the_same(&other@[i]);
        }
        lemma_fold_left_on_equiv_seqs(self@.subrange(0, idx), other@.subrange(0, idx), |x: T, y: T| g(x) == g(y), emp, accg);
      }
      assert(
        ((self@.len() as usize).ghost_serialize() + gs(self@, 0, idx))
        ==
        ((other@.len() as usize).ghost_serialize() + gs(other@, 0, idx))
      );
      let prefix_len = ((self@.len() as usize).ghost_serialize() + gs(self@, 0, idx)).len();
      let i = if g(self@[idx]).len() <= g(other@[idx]).len() {
        self@[idx].lemma_serialization_is_not_a_prefix_of(&other@[idx]);
        some_differing_index_for_unequal_seqs(g(self@[idx]), g(other@[idx]).subrange(0, g(self@[idx]).len() as int))
      } else {
        self@[idx].lemma_view_equal_symmetric(&other@[idx]);
        other@[idx].lemma_serialization_is_not_a_prefix_of(&self@[idx]);
        some_differing_index_for_unequal_seqs(g(other@[idx]), g(self@[idx]).subrange(0, g(other@[idx]).len() as int))
      };
      assert(g(self@[idx])[i] != g(other@[idx])[i]);
      assert(self.ghost_serialize()[prefix_len + i] != other.ghost_serialize()[prefix_len + i]);
      assert(self.ghost_serialize() != other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int));
    }
  }

	#[verifier::external_body]
  #[verifier::spinoff_prover]
  proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)
	{
		unimplemented!()
	}

}



}
