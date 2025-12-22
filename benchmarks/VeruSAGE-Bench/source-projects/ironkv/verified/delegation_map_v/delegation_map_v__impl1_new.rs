use vstd::prelude::*;

fn main() {}


verus! {
type ID = EndPoint;

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}


impl Ordering {

    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }
}

struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool
{
    forall |i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedVec<K> {

    pub closed spec fn view(self) -> Seq<K> {
        self.v@
    }

    pub closed spec fn valid(self) -> bool {
        sorted(self@) && self@.no_duplicates()
    }

    fn new() -> (v: Self)
        ensures v@ == Seq::<K>::empty(),
                v.valid(),
    {
        StrictlyOrderedVec { v: Vec::new() }
    }
}

#[verifier::reject_recursive_types(K)]

struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

#[verifier::reject_recursive_types(K)]

pub struct DelegationMap<K: KeyTrait + VerusClone> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,

}


pub struct EndPoint {
    pub id: Vec<u8>,
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub trait KeyTrait : Sized {

    spec fn cmp_spec(self, other: Self) -> Ordering;

}

pub trait VerusClone : Sized {}

}
