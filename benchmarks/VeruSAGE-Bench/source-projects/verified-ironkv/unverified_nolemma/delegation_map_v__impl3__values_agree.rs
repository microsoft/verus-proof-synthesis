use vstd::prelude::*;
fn main() {}
verus! {

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

type ID = EndPoint;

pub struct EndPoint {
    pub id: Vec<u8>,
}

impl EndPoint {
    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }
}

#[verifier::external_body]
pub fn do_end_points_match(e1: &EndPoint, e2: &EndPoint) -> (eq: bool)
    ensures
        eq == (e1@ == e2@),
{
    unimplemented!()
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
}

#[verifier::reject_recursive_types(K)]
struct StrictlyOrderedMap<K: KeyTrait + VerusClone> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<ID>,
    m: Ghost<Map<K, ID>>,
}

impl<K: KeyTrait + VerusClone> StrictlyOrderedMap<K> {
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

    fn values_agree(&self, lo: usize, hi: usize, v: &ID) -> (ret: (bool, bool))
        requires
            self.valid(),
            0 <= lo <= hi < self.keys@.len(),
        ensures
            ret.0 == forall|i| #![auto] lo <= i <= hi ==> self.vals@[i]@ == v@,
            !ret.0 ==> (ret.1 == (self.vals@[hi as int]@ != v@ && forall|i|
                #![auto]
                lo <= i < hi ==> self.vals@[i]@ == v@)),
    {
        {
        let mut i = lo;
        while i <= hi {
            let eq = do_end_points_match(&self.vals[i], v);
            if  !eq {
                if i == hi {
                    let ret = (false, true);
                    return ret;
                } else {
                    let ret = (false, false);
                    return ret;
                }
            } else {
            }
            i = i + 1;
        }
        let ret = (true, true);
        ret
    }
    }
}

} // verus!
