use vstd::bytes::*;
use vstd::prelude::*;
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
    exec fn serialize(&self, data: &mut Vec<u8>)
        requires
            self.is_marshalable(),
        ensures
            data@.len() >= old(data).len(),
            data@.subrange(0, old(data)@.len() as int) == old(data)@,
            data@.subrange(old(data)@.len() as int, data@.len() as int) == self.ghost_serialize(),
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
    exec fn serialize(&self, data: &mut Vec<u8>) {
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
    exec fn serialize(&self, data: &mut Vec<u8>) {
        unimplemented!()
    }
}

impl Marshalable for Vec<u8> {
    open spec fn is_marshalable(&self) -> bool {
        self@.len() <= usize::MAX && (self@.len() as usize).ghost_serialize().len()
            + self@.len() as int <= usize::MAX
    }

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        (self@.len() as usize).ghost_serialize() + self@
    }

    #[verifier::external_body]
    exec fn serialize(&self, data: &mut Vec<u8>) {
        unimplemented!()
    }
}

impl<T: Marshalable> Marshalable for Vec<T> {
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

    exec fn serialize(&self, data: &mut Vec<u8>) {
        let self_len = self.len();
        self_len.serialize(data);
        let mut i: usize = 0;
        while i < self.len() {
            self[i].serialize(data);
            i = i + 1;
        }
    }
}

} // verus!
