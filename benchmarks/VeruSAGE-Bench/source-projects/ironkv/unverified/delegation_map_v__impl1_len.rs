use vstd::prelude::*;
fn main() {}
verus! {

type ID = EndPoint;

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

#[verifier::reject_recursive_types(K)]
struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    lows: StrictlyOrderedMap<K>,
    m: Ghost<Map<K, AbstractEndPoint>>,
}

pub struct EndPoint {
    pub id: Vec<u8>,
}

pub trait VerusClone: Sized {
    fn clone(&self) -> (o: Self)
        ensures
            o == self,
    ;
}

pub trait KeyTrait: Sized {

}

impl<K: KeyTrait + VerusClone> StrictlyOrderedVec<K> {
    pub closed spec fn view(self) -> Seq<K> {
        self.v@
    }

    fn len(&self) -> (len: usize)
        ensures
            len == self@.len(),
    {
        let ret = self.v.len();
        ret
    }
}

} // verus!
