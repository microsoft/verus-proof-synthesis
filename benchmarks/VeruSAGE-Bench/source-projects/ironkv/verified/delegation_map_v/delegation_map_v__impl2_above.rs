use vstd::prelude::*;

fn main() {}

verus! {

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl Ordering{
    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }

	#[verifier::external_body]
    pub const fn is_lt(self) -> (b:bool)
        ensures b == self.lt(),
	{
		unimplemented!()
	}
}

struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {


    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

	#[verifier::external_body]
    pub fn is_end(&self) -> (b: bool)
        ensures b == self.is_end_spec()
	{
		unimplemented!()
	}

    spec fn above_spec(&self, k: K) -> bool {
        self.k.is_None() || k.cmp_spec(self.k.get_Some_0()).lt()
    }

    fn above(&self, k: K) -> (b: bool)
        ensures b == self.above_spec(k),
    {
        self.is_end() || k.cmp(&self.k.as_ref().unwrap().clone()).is_lt()
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


pub trait KeyTrait : Sized {

    spec fn cmp_spec(self, other: Self) -> Ordering;

    fn cmp(&self, other: &Self) -> (o: Ordering)
        requires true,
        ensures o == self.cmp_spec(*other);
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

type ID = EndPoint;

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    // None means we hit the end
    pub k: Option<K>,
}

pub trait VerusClone : Sized {}
}
