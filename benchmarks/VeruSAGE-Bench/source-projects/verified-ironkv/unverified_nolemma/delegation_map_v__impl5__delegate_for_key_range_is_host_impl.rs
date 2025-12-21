use vstd::prelude::*;
fn main() {}
verus! {

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

impl AbstractEndPoint {
    pub open spec fn valid_physical_address(self) -> bool {
        self.id.len() < 0x100000
    }
}

pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {
    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }
}

type ID = EndPoint;

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

impl Ordering {
    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }
}

pub trait KeyTrait: Sized {
    spec fn zero_spec() -> Self where Self: std::marker::Sized;
    spec fn cmp_spec(self, other: Self) -> Ordering;
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool {
    forall|i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
}

pub trait VerusClone: Sized {}

pub struct KeyIterator<K: KeyTrait + VerusClone> {
    pub k: Option<K>,
}

impl<K: KeyTrait + VerusClone> KeyIterator<K> {
    pub open spec fn new_spec(k: K) -> Self {
        KeyIterator { k: Some(k) }
    }

    pub open spec fn lt_spec(self, other: Self) -> bool {
        (!self.k.is_None() && other.k.is_None()) || (!self.k.is_None() && !other.k.is_None()
            && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }
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

    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(lhs) && ki.lt_spec(rhs)
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires
            !self.is_end(),
        ensures
            k == self.get_spec(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures
            b == self.is_end_spec(),
    {
        unimplemented!()
    }
}


pub struct KeyRange<K: KeyTrait + VerusClone> {
    pub lo: KeyIterator<K>,
    pub hi: KeyIterator<K>,
}

impl<K: KeyTrait + VerusClone> KeyRange<K> {
    pub open spec fn contains(self, k: K) -> bool {
        KeyIterator::<K>::between(self.lo, KeyIterator::<K>::new_spec(k), self.hi)
    }
}

pub struct SHTKey {
    pub ukey: u64,
}

impl KeyTrait for SHTKey {
    open spec fn zero_spec() -> Self {
        SHTKey { ukey: 0 }
    }

    open spec fn cmp_spec(self, other: Self) -> Ordering {
        if self.ukey < other.ukey {
            Ordering::Less
        } else if self.ukey == other.ukey {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

impl VerusClone for SHTKey {}

pub type AbstractKey = SHTKey;

pub struct AbstractDelegationMap(pub Map<AbstractKey, AbstractEndPoint>);

impl AbstractDelegationMap {
    pub open spec fn view(self) -> Map<AbstractKey, AbstractEndPoint> {
        self.0
    }

    pub open spec fn spec_index(self, key: AbstractKey) -> AbstractEndPoint
        recommends
            self.0.dom().contains(key),
    {
        self@.index(key)
    }

    pub open spec fn is_complete(self) -> bool {
        self@.dom().is_full()
    }

    pub open spec fn delegate_for_key_range_is_host(
        self,
        kr: KeyRange<AbstractKey>,
        id: AbstractEndPoint,
    ) -> bool
        recommends
            self.is_complete(),
    {
        forall|k: AbstractKey| #[trigger] kr.contains(k) ==> self[k] == id
    }
}


struct StrictlyOrderedVec<K: KeyTrait> {
    v: Vec<K>,
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedVec<K> {
    pub closed spec fn view(self) -> Seq<K> {
        self.v@
    }

    pub closed spec fn valid(self) -> bool {
        sorted(self@) && self@.no_duplicates()
    }
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

    pub closed spec fn map_valid(self) -> bool {
        &&& self.m@.dom().finite()
        &&& self.m@.dom() == self.keys@.to_set()
        &&& forall|i|
            0 <= i < self.keys@.len() ==> #[trigger] (self.m@[self.keys@.index(i)])
                == self.vals@.index(i)
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.keys.valid()
        &&& self.keys@.len() == self.vals.len()
        &&& self.map_valid()
    }

    spec fn gap(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> bool {
        forall|ki| lo.lt_spec(ki) && ki.lt_spec(hi) ==> !(#[trigger] self@.contains_key(*ki.get()))
    }
}

#[verifier::reject_recursive_types(K)]
pub struct DelegationMap<K: KeyTrait + VerusClone> {
    lows: StrictlyOrderedMap<K>,
    m: Ghost<Map<K, AbstractEndPoint>>,
}

impl<K: KeyTrait + VerusClone> DelegationMap<K> {
    pub closed spec fn view(self) -> Map<K, AbstractEndPoint> {
        self.m@
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.lows.valid()
        &&& self.lows@.contains_key(K::zero_spec())
        &&& self@.dom().is_full()
        &&& (forall|k| #[trigger] self@[k].valid_physical_address())
        &&& (forall|k, i, j|
            self.lows@.contains_key(i) && self.lows.gap(KeyIterator::new_spec(i), j)
                && #[trigger] KeyIterator::between(
                KeyIterator::new_spec(i),
                KeyIterator::new_spec(k),
                j,
            ) ==> self@[k] == self.lows@[i]@)
    }

    pub open spec fn range_consistent(
        self,
        lo: &KeyIterator<K>,
        hi: &KeyIterator<K>,
        dst: &ID,
    ) -> bool {
        forall|k|
            KeyIterator::between(*lo, KeyIterator::new_spec(k), *hi) ==> (#[trigger] self@[k])
                == dst@
    }

    #[verifier::external_body]
    pub fn range_consistent_impl(&self, lo: &KeyIterator<K>, hi: &KeyIterator<K>, dst: &ID) -> (b:
        bool)
        requires
            self.valid(),
        ensures
            b == self.range_consistent(lo, hi, dst),
    {
        unimplemented!()
    }
}

impl DelegationMap<AbstractKey> {
    pub fn delegate_for_key_range_is_host_impl(
        &self,
        lo: &KeyIterator<AbstractKey>,
        hi: &KeyIterator<AbstractKey>,
        dst: &ID,
    ) -> (b: bool)
        requires
            self.valid(),
        ensures
            b == AbstractDelegationMap::delegate_for_key_range_is_host(
                AbstractDelegationMap(self@),
                KeyRange { lo: *lo, hi: *hi },
                dst@,
            ),
    {
        let ret = self.range_consistent_impl(lo, hi, dst);
        ret
    }
}

} // verus!
