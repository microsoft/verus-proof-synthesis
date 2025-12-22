use vstd::prelude::*;
use vstd::set_lib::*;

fn main() {}


verus! {

type ID = EndPoint;

impl Ordering{

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

    fn remove(&mut self, i: usize) -> (k: K)
        requires
            old(self).valid(),
            i < old(self)@.len(),
        ensures
            self.valid(),
            k == old(self)@.index(i as int),
            self@ == old(self)@.remove(i as int),
            self@.to_set() == old(self)@.to_set().remove(k),
    {
        let k = self.v.remove(i);
        proof {
            let old_s = old(self)@.to_set().remove(k);
            let new_s = self@.to_set();
            assert forall |e| old_s.contains(e) implies new_s.contains(e) by {
                assert(old(self)@.to_set().contains(e));
                let n = choose |n: int| 0 <= n < old(self)@.len() && old(self)@[n] == e;
                if n < i {
                    assert(self@[n] == e);  // OBSERVE
                } else {
                    assert(self@[n-1] == e);  // OBSERVE
                }
            }
            assert_sets_equal!(self@.to_set(), old(self)@.to_set().remove(k));
        }
        k
    }
}

pub struct EndPoint {
    pub id: Vec<u8>,
}

pub trait KeyTrait : Sized {

    spec fn cmp_spec(self, other: Self) -> Ordering;
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub trait VerusClone : Sized {
}


}
