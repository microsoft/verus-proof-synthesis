use vstd::bytes::*;
use vstd::prelude::*;
use vstd::slice::*;
fn main() {}
verus! {

pub trait Marshalable: Sized {
    spec fn is_marshalable(&self) -> bool;

    #[verifier::external_body]
    spec fn ghost_serialize(&self) -> Seq<u8>
        recommends
            self.is_marshalable(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    exec fn serialized_size(&self) -> (res: usize)
        requires
            self.is_marshalable(),
        ensures
            res as int == self.ghost_serialize().len(),
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
    exec fn serialized_size(&self) -> (res: usize) {
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

    exec fn serialized_size(&self) -> (res: usize) {
        (*self as u64).serialized_size()
    }
}

} // verus!
