use vstd::prelude::*;
use vstd::bytes::*;

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
      data@.subrange(old(data)@.len() as int, data@.len() as int) == self.ghost_serialize()
  {unimplemented!()}

}


impl Marshalable for u64 {

  open spec fn is_marshalable(&self) -> bool {
    true
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    spec_u64_to_le_bytes(*self)
  }

	#[verifier::external_body]
  exec fn serialize(&self, data: &mut Vec<u8>)
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


impl<T: Marshalable, U: Marshalable> Marshalable for (T, U) {

  open spec fn is_marshalable(&self) -> bool {
    &&& self.0.is_marshalable()
    &&& self.1.is_marshalable()
    &&& self.0.ghost_serialize().len() + self.1.ghost_serialize().len() <= usize::MAX
  }

  open spec fn ghost_serialize(&self) -> Seq<u8> {
    self.0.ghost_serialize() + self.1.ghost_serialize()
  }

#[verifier::spinoff_prover]
  exec fn serialize(&self, data: &mut Vec<u8>)
    // req, ens from trait
  {
    self.0.serialize(data);
    // assert(data@.subrange(0, old(data)@.len() as int) == old(data)@);

    let mid_data_len: Ghost<int> = Ghost(data@.len() as int);

    self.1.serialize(data);

    proof {
      assert(data@.subrange(0, old(data)@.len() as int) =~= data@.subrange(0, mid_data_len@).subrange(0, old(data)@.len() as int));
      // assert(data@.subrange(0, old(data)@.len() as int) == old(data)@);
      assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= data@.subrange(0, mid_data_len@).subrange(old(data)@.len() as int, mid_data_len@));
      // assert(data@.subrange(old(data)@.len() as int, mid_data_len@) == self.0.ghost_serialize());
      // assert(data@.subrange(mid_data_len@, data@.len() as int) == self.1.ghost_serialize());
      assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.0.ghost_serialize() + self.1.ghost_serialize());
    }
  }

}



}
