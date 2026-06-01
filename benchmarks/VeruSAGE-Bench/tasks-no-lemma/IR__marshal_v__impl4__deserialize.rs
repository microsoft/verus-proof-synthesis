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
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)
        ensures
            match res {
                Some((x, end)) => {
                    &&& x.is_marshalable()
                    &&& start <= end <= data.len()
                    &&& data@.subrange(start as int, end as int) == x.ghost_serialize()
                },
                None => true,
            },
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
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>) {
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
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>) {
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
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>) {
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

    open spec fn ghost_serialize(&self) -> Seq<u8> {
        match self {
            None => seq![0],
            Some(x) => seq![1] + x.ghost_serialize(),
        }
    }

    #[verifier::external_body]
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>) {
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
    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>) {
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

    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>) {
        let (len, mid) = match usize::deserialize(data, start) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let len = len as usize;
        let mut res: Vec<T> = Vec::with_capacity(len);
        let mut i: usize = 0;
        let mut end = mid;
        while i < len {
            let (x, end1) = match T::deserialize(data, end) {
                None => {
                    return None;
                },
                Some(x) => x,
            };
            res.push(x);
            end = end1;
            i = i + 1;
        }
        let ret = Some((res, end));
        ret
    }
}

} // verus!
