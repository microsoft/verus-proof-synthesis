use vstd::prelude::*;
use vstd::bytes::*;

fn main() {}

verus!{

// File: verus_extra/seq_lib_v.rs
	#[verifier::external_body]
pub proof fn lemma_seq_fold_left_sum_right<A>(s: Seq<A>, low: int, f: spec_fn(A) -> int)
  requires
    s.len() > 0,
  ensures
    s.subrange(0, s.len() - 1).fold_left(low, |b: int, a: A| b + f(a)) + f(s[s.len() - 1])
    ==
    s.fold_left(low, |b: int, a: A| b + f(a))
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn lemma_seq_fold_left_append_len_int_le<A, B>(s: Seq<A>, i: int, low: int, f: spec_fn(A) -> Seq<B>)
  requires
    0 <= i <= s.len() as int,
    0 <= low,
  ensures
    s.fold_left(low, |acc: int, x: A| acc + f(x).len()) >= 0,
    s.subrange(0, i).fold_left(low, |acc: int, x: A| acc + f(x).len()) <=
    s.fold_left(low, |acc: int, x: A| acc + f(x).len()),
  decreases (2 * s.len() - i),
	{
		unimplemented!()
	}


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  exec fn _is_marshalable(&self) -> (res: bool)
    ensures res == self.is_marshalable()
  {unimplemented!()}

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable()
  {unimplemented!()}

	#[verifier::external_body]
  exec fn serialized_size(&self) -> (res: usize)
    requires self.is_marshalable(),
    ensures res as int == self.ghost_serialize().len(),
  {unimplemented!()}

}


impl Marshalable for u64 {

  open spec fn is_marshalable(&self) -> bool {
    true
  }

	#[verifier::external_body]
  exec fn _is_marshalable(&self) -> (res: bool)
	{
		unimplemented!()
	}

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    spec_u64_to_le_bytes(*self)
  }

	#[verifier::external_body]
  #[verifier::spinoff_prover]
  exec fn serialized_size(&self) -> (res: usize)
	{
		unimplemented!()
	}

}


impl Marshalable for usize {

  open spec fn is_marshalable(&self) -> bool {
    &&& *self as int <= u64::MAX
  }

	#[verifier::external_body]
  exec fn _is_marshalable(&self) -> (res: bool)
	{
		unimplemented!()
	}

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (*self as u64).ghost_serialize()
  }

	#[verifier::external_body]
  exec fn serialized_size(&self) -> (res: usize)
	{
		unimplemented!()
	}

}


impl Marshalable for Vec<u8> {

  open spec fn is_marshalable(&self) -> bool {
    self@.len() <= usize::MAX &&
    (self@.len() as usize).ghost_serialize().len() + self@.len() as int <= usize::MAX
  }

	#[verifier::external_body]
  exec fn _is_marshalable(&self) -> (res: bool)
	{
		unimplemented!()
	}

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@
  }

	#[verifier::external_body]
  exec fn serialized_size(&self) -> (res: usize)
	{
		unimplemented!()
	}

}


impl<T: Marshalable> Marshalable for Vec<T> {

  open spec fn is_marshalable(&self) -> bool {
    &&& self@.len() <= usize::MAX
    &&& (forall |x: T| self@.contains(x) ==> #[trigger] x.is_marshalable())
    &&& (self@.len() as usize).ghost_serialize().len() +
        self@.fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()) <= usize::MAX
  }

  #[verifier::spinoff_prover]
  exec fn _is_marshalable(&self) -> bool {
    let mut res = true;
    let mut i = 0;
    let mut total_len = self.len().serialized_size();

    proof {
      assert(self@ =~= self@.subrange(0, self@.len() as int));
    }

    while res && i < self.len()
      invariant
        0 <= i <= self.len(),
        res ==> total_len as int == (self@.len() as usize).ghost_serialize().len() +
                 self@.subrange(0, i as int).fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()),
        res ==> (forall |x: T| self@.subrange(0, i as int).contains(x) ==> #[trigger] x.is_marshalable()),
        res ==> total_len as int <= usize::MAX,
        !res ==> !self.is_marshalable(),
      decreases
        self.len() - i + if res { 1int } else { 0int }
    {
      assert(res);
      res = res && self[i]._is_marshalable() && (usize::MAX - total_len >= self[i].serialized_size());
      if res {
        let old_total_len = total_len;
        total_len = total_len + self[i].serialized_size();
        i = i + 1;
        proof {
          assert forall |x: T| #[trigger] self@.subrange(0, i as int).contains(x) implies x.is_marshalable() by {
            if (exists |j:int| 0 <= j < self@.subrange(0, i as int).len() - 1 && self@.subrange(0, i as int)[j] == x) {
              let j = choose|j:int| 0 <= j < self@.subrange(0, i as int).len() - 1 && self@.subrange(0, i as int)[j] == x;
              assert(self@.subrange(0, i as int - 1)[j] == x); // OBSERVE
            }
          };
          let sl = |x: T| x.ghost_serialize().len() as int;
          assert((|acc: int, x: T| acc + x.ghost_serialize().len() as int) =~= (|acc: int, x: T| acc + sl(x)));
          let s = self@.subrange(0 as int, i as int);
          lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
          assert(s.subrange(0, s.len() - 1) =~= self@.subrange(0 as int, i - 1 as int));
        }
      } else {
        proof {
          if usize::MAX < total_len + self@[i as int].ghost_serialize().len() {
            assert(
              ((self@.len() as usize).ghost_serialize().len() +
               self@.fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()))
                >=
              (total_len + self@[i as int].ghost_serialize().len())
            ) by {
              let f = |x: T| x.ghost_serialize();
              let sl = |x: T| x.ghost_serialize().len() as int;
              let s = self@.subrange(0 as int, i as int + 1);
              assert((|acc: int, x: T| acc + x.ghost_serialize().len() as int) =~= (|acc: int, x: T| acc + sl(x)));
              lemma_seq_fold_left_sum_right::<T>(s, 0, sl);
              assert(s.subrange(0, s.len() - 1) =~= self@.subrange(0 as int, i as int));
              lemma_seq_fold_left_append_len_int_le(self@, i as int + 1, 0, f);
              assert((|acc: int, x: T| acc + x.ghost_serialize().len() as int) =~= (|acc: int, x: T| acc + f(x).len()));
            };
          } else {
            assert(!self@[i as int].is_marshalable());
          }
        }
      }
    }

    res
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@.fold_left(Seq::<u8>::empty(), |acc: Seq<u8>, x: T| acc + x.ghost_serialize())
  }

	#[verifier::external_body]
  #[verifier::spinoff_prover]
  exec fn serialized_size(&self) -> (res: usize)
	{
		unimplemented!()
	}

}



}
