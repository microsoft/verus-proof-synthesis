use vstd::prelude::*;
fn main() {}
verus! {

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

#[verifier::reject_recursive_types(K)]
struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedMap<K> {
    pub closed spec fn view(self) -> Map<K, ID> {
        self.m@
    }

    spec fn gap(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> bool {
        forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) ==> !(#[trigger] self@.contains_key(*ki.get()))
    }

    proof fn choose_gap_violator(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> (r: KeyIterator<
        K,
    >)
        requires
            !self.gap(lo, hi),
        ensures
            lo.lt_spec(r) && r.lt_spec(hi) && self@.contains_key(*r.get()),
    {
        proof_from_false() // TODO - replace with correct value
    }
}

#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    lows: StrictlyOrderedMap<K>,
    m: Ghost<Map<K, AbstractEndPoint>>,
}

pub struct EndPoint {
    pub id: Vec<u8>,
}

type ID = EndPoint;

pub trait KeyTrait: Sized {
    spec fn cmp_spec(self, other: Self) -> Ordering;
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None()) || (!self.k.is_None() && !other.k.is_None()
            && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }
}

pub trait VerusClone: Sized {

}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn get_spec(&self) -> &K
        recommends
            self.k.is_some(),
    {
        &self.k.get_Some_0()
    }

    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires
            !self.is_end(),
        ensures
            k == self.get_spec(),
    {
        self.k.as_ref().unwrap()
    }

    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures
            b == self.is_end_spec(),
    {
        matches!(self.k, None)
    }
}

} // verus!
