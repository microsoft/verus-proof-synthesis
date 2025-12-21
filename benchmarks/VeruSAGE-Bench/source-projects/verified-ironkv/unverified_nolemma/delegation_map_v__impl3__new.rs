use vstd::prelude::*;

fn main() {}

verus! {

type ID = EndPoint;

pub struct EndPoint {
    pub id: Vec<u8>,
}

pub trait VerusClone: Sized {}

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
    spec fn cmp_spec(self, other: Self) -> Ordering;
}

spec fn sorted<K: KeyTrait>(s: Seq<K>) -> bool {
    forall|i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
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

    #[verifier::external_body]
    fn new() -> (v: Self)
        ensures
            v@ == Seq::<K>::empty(),
            v.valid(),
    {
        unimplemented!()
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

    fn new() -> (s: Self)
        ensures
            s.valid(),
            s@ == Map::<K, ID>::empty(),
    {
        let keys = StrictlyOrderedVec::new();
        let ghost m_ghost: Map<K, ID> = arbitrary(); // TODO - replace with correct value
        let m = Ghost(m_ghost);
        let ret = StrictlyOrderedMap { keys, vals: Vec::new(), m };
        ret
    }
}

} // verus!
