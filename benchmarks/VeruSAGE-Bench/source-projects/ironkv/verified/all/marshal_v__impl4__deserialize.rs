use vstd::prelude::*;
use vstd::bytes::*;

fn main() {}

verus!{

// File: verus_extra/seq_lib_v.rs
	#[verifier::external_body]
pub proof fn lemma_seq_add_subrange<A>(s: Seq<A>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= s.len(),
  ensures s.subrange(i, j) + s.subrange(j, k) == s.subrange(i, k),
	{
		unimplemented!()
	}

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
pub proof fn lemma_seq_fold_left_append_right<A, B>(s: Seq<A>, prefix: Seq<B>, f: spec_fn(A) -> Seq<B>)
  requires s.len() > 0,
  ensures
    s.subrange(0, s.len() - 1).fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)) + f(s[s.len() - 1])
    ==
    s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a))
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

	#[verifier::external_body]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
    ensures match res {
      Some((x, end)) => {
        &&& x.is_marshalable()
        &&& start <= end <= data.len()
        &&& data@.subrange(start as int, end as int) == x.ghost_serialize()
      }
      None => true,
  }
	{
		unimplemented!()
	}

}


impl Marshalable for u64 {

  open spec fn is_marshalable(&self) -> bool {
    true
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    spec_u64_to_le_bytes(*self)
  }

	#[verifier::external_body]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
	{
		unimplemented!()
	}

}


impl Marshalable for usize {

  open spec fn is_marshalable(&self) -> bool {
    &&& *self as int <= u64::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (*self as u64).ghost_serialize()
  }

	#[verifier::external_body]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
	{
		unimplemented!()
	}

}


impl Marshalable for Vec<u8> {

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
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
	{
		unimplemented!()
	}

}


impl<T: Marshalable> Marshalable for Option<T> {

  open spec fn is_marshalable(&self) -> bool {
    match self {
      None => true,
      Some(x) => x.is_marshalable() && 1 + x.ghost_serialize().len() <= usize::MAX,
    }
  }

  open spec fn ghost_serialize(&self) -> Seq<u8>
  // req, ens from trait
  {
    match self {
      None => seq![0],
      Some(x) => seq![1] + x.ghost_serialize(),
    }
  }

	#[verifier::external_body]
  #[verifier::spinoff_prover]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
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

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    (self@.len() as usize).ghost_serialize()
      + self@.fold_left(Seq::<u8>::empty(), |acc: Seq<u8>, x: T| acc + x.ghost_serialize())
  }

  #[verifier::spinoff_prover]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
    // req, ens from trait
  {
    let (len, mid) = match usize::deserialize(data, start) { None => {
      return None;
    }, Some(x) => x, };
    let len = len as usize;

    let mut res: Vec<T> = Vec::with_capacity(len);
    let mut i: usize = 0;
    let mut end = mid;

    let emp: Ghost<Seq<u8>> = Ghost(Seq::<u8>::empty());
    let accf: Ghost<spec_fn(Seq<u8>, T) -> Seq<u8>> = Ghost(|acc: Seq<u8>, x: T| acc + x.ghost_serialize());

    proof {
      assert(data@.subrange(mid as int, end as int) =~= emp@);
      // assert(emp == seq_lib_v::seq_fold_left(res@, emp@, accf@));

      lemma_auto_spec_u64_to_from_le_bytes();
    }

    while i < len
      invariant
        0 <= i <= len,
        res.is_marshalable(),
        start <= mid <= end <= data@.len(),
        data@.subrange(mid as int, end as int) == res@.fold_left(emp@, accf@),
        res@.len() == i,
        len.ghost_serialize().len() +
          res@.fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()) == end - start,
        accf@ == |acc: Seq<u8>, x: T| acc + x.ghost_serialize(),
      decreases
        len - i
    {
      let (x, end1) = match T::deserialize(data, end) { None => {
        return None;
      }, Some(x) => x, };

      let old_end: Ghost<int> = Ghost(end as int);
      let old_res: Ghost<Seq<T>> = Ghost(res@);

      res.push(x);
      end = end1;
      i = i + 1;

      assert(data@.subrange(mid as int, end as int) == res@.fold_left(emp@, accf@)) by {
        let f = |x: T| x.ghost_serialize();
        // assert(data@.subrange(mid as int, old_end@) == seq_lib_v::seq_fold_left(old_res@, emp@, accf@));
        lemma_seq_add_subrange::<u8>(data@, mid as int, old_end@, end as int);
        // assert(data@.subrange(mid as int, end as int) ==
        //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + data@.subrange(old_end@, end as int));
        // assert(data@.subrange(mid as int, end as int) ==
        //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + x.ghost_serialize());
        // assert(f(x) == x.ghost_serialize());
        // assert(data@.subrange(mid as int, end as int) ==
        //        seq_lib_v::seq_fold_left(old_res@, emp@, accf@) + f(x));
        lemma_seq_fold_left_append_right(res@, emp@, f);
        assert(accf@ == (|acc: Seq<u8>, x: T| acc + f(x))) by {
          assert(accf@ =~= (|acc: Seq<u8>, x: T| acc + f(x)));
        }
        assert(old_res@ =~= res@.subrange(0, res@.len() - 1));
        // assert(data@.subrange(mid as int, end as int) == seq_lib_v::seq_fold_left(res@, emp@, accf@));
      }

      assert (len.ghost_serialize().len() +
              res@.fold_left(0, |acc: int, x: T| acc + x.ghost_serialize().len()) == end - start) by {
        let l = |x: T| x.ghost_serialize().len() as int;
        let suml = |acc: int, x: T| acc + l(x);
        lemma_seq_fold_left_sum_right(res@, 0, l);
        assert((|acc: int, x: T| acc + x.ghost_serialize().len()) =~= suml);
        assert(old_res@ =~= res@.subrange(0, res@.len() - 1));
      }

      assert (len.ghost_serialize().len() == (res@.len() as usize).ghost_serialize().len()) by {
        lemma_auto_spec_u64_to_from_le_bytes();
      }
    }
    assert(data@.subrange(start as int, end as int) == res.ghost_serialize()) by {
      lemma_seq_add_subrange::<u8>(data@, start as int, mid as int, end as int);
    }

    Some((res, end))
  }

}


impl<T: Marshalable, U: Marshalable> Marshalable for (T, U) {

  open spec fn is_marshalable(&self) -> bool {
    &&& self.0.is_marshalable()
    &&& self.1.is_marshalable()
    &&& self.0.ghost_serialize().len() + self.1.ghost_serialize().len() <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    self.0.ghost_serialize() + self.1.ghost_serialize()
  }

	#[verifier::external_body]
#[verifier::spinoff_prover]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
	{
		unimplemented!()
	}

}



}
