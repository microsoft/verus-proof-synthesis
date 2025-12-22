use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use vstd::bytes::*;
use vstd::slice::*;

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


// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable(),
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

  #[verifier::spinoff_prover]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
    // req, ens from trait
  {
    let (len, mid) = match usize::deserialize(data, start) { None => {
      return None;
    }, Some(x) => x, };
    let len = len as usize;

    // assert(mid <= data.len());
    // assert(data@.subrange(start as int, mid as int) == usize(len).ghost_serialize());

    let end = if usize::MAX - mid >= len {
      mid + len
    } else {
      return None;
    };
    if end > data.len() {
      return None;
    }

    // assert(0 <= mid);
    // assert(len >= 0);
    // assert(mid <= end);
    // assert(end <= data.len());
    let res_slice = slice_subrange(data.as_slice(), mid, end);
    let res = slice_to_vec(res_slice);

    // assert(res_slice@ == data@.subrange(mid as int, end as int));
    // assert(res@ == res_slice@);

    // assert(res.ghost_serialize() == usize(len).ghost_serialize() + res@);
    // assert(data@.subrange(start as int, mid as int) == usize(len).ghost_serialize());
    // assert(data@.subrange(mid as int, end as int) == res@);

    // assert(0 <= start);
    // assert(start <= mid);
    // assert(mid <= end);
    // assert(end <= data.len());

    proof {
      // We split this part of the proof out into a lemma due to verifier performance issues;
      // with the lemma inlined, the proof failed.
      // This is surprising verifier behavior because the lemma only calls the `assert_seqs_equal!`
      // macro which itself only uses `assert by` which should preclude verifier performance
      // misbehavior.
      lemma_seq_add_subrange::<u8>(data@, start as int, mid as int, end as int);
    }

    Some((res, end))
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

	#[verifier::external_body]
  #[verifier::spinoff_prover]
  exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
	{
		unimplemented!()
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
