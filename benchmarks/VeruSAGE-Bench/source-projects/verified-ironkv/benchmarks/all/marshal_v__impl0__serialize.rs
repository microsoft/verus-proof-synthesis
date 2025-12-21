use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use vstd::bytes::*;
use vstd::slice::*;

fn main() {}

verus!{

// File: marshal_v.rs
pub trait Marshalable : Sized {

  spec fn is_marshalable(&self) -> bool;

	#[verifier::external_body]
  spec fn ghost_serialize(&self) -> Seq<u8>
    recommends self.is_marshalable()
  {unimplemented!()}

	#[verifier::external_body]
  exec fn serialize(&self, data: &mut Vec<u8>)
    requires self.is_marshalable()
    ensures
      data@.len() >= old(data).len(),
      data@.subrange(0, old(data)@.len() as int) == old(data)@,
      data@.subrange(old(data)@.len() as int, data@.len() as int) == self.ghost_serialize(),
  {unimplemented!()}

}


impl Marshalable for u64 {

  open spec fn is_marshalable(&self) -> bool {
    true
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    spec_u64_to_le_bytes(*self)
  }

  exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
  {
    let s = u64_to_le_bytes(*self);
    let mut i: usize = 0;

    proof {
      assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
      assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize().subrange(0, i as int));
      lemma_auto_spec_u64_to_from_le_bytes();
    }

    while i < 8
      invariant
        0 <= i <= 8,
        s.len() == 8,
        s@ == self.ghost_serialize(),
        data@.subrange(0, old(data)@.len() as int) == old(data)@,
        data@.subrange(old(data)@.len() as int, data@.len() as int) == self.ghost_serialize().subrange(0, i as int),
        data@.len() == old(data)@.len() + i as int,
      decreases
        8 - i
    {
      assert(data@.subrange(old(data)@.len() as int, data@.len() as int) == data@.subrange(old(data)@.len() as int, old(data)@.len() + i as int));

      let x: u8 = s[i];
      data.push(x);
      i = i + 1;

      proof {
        assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);
        assert (data@.subrange(old(data)@.len() as int, data@.len() as int) == self.ghost_serialize().subrange(0, i as int)) by {
          assert(self.ghost_serialize().subrange(0, (i - 1) as int).push(x) =~= self.ghost_serialize().subrange(0, i as int));
          assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize().subrange(0, (i - 1) as int).push(x));
        }
      }
    }

    proof {
      assert(self.ghost_serialize().subrange(0, i as int) =~= self.ghost_serialize());
    }
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
  exec fn serialize(&self, data: &mut Vec<u8>)
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
  exec fn serialize(&self, data: &mut Vec<u8>)
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
  exec fn serialize(&self, data: &mut Vec<u8>)
	{
		unimplemented!()
	}

}



}
