use vstd::prelude::*;

fn main() {}

verus! {

type ID = EndPoint;

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl Ordering {

    pub open spec fn ge(self) -> bool {
        !matches!(self, Ordering::Less)
    }

    //Target function
    pub const fn is_ge(self) -> (b:bool)
        ensures b == self.ge(),
    {
        !matches!(self, Ordering::Less)
    }
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
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K>,
    // Our spec version
    m: Ghost<Map<K, AbstractEndPoint>>,

}


 #[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}


pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub trait KeyTrait : Sized {
}

pub trait VerusClone : Sized {
    fn clone(&self) -> (o: Self)
        ensures o == self;  // this is way too restrictive; it kind of demands Copy. But we don't have a View trait yet. :v(
}

}
