use vstd::prelude::*;
fn main() {}
verus! {

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

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

type ID = EndPoint;

pub trait KeyTrait: Sized {

}

pub trait VerusClone: Sized {

}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub fn new(k: K) -> (s: Self)
        ensures
            s.k == Some(k),
    {
        let ret = KeyIterator { k: Some(k) };
        ret
    }
}

} // verus!
