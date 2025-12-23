use vstd::prelude::*;
use vstd::set_lib::*;

fn main() {}


verus! {

type ID = EndPoint;

pub struct AbstractEndPoint {
    pub id: Seq<u8>,
}

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
            assert(self@.to_set() =~= old(self)@.to_set().remove(k)) by {
                assert forall |e| old(self)@.to_set().remove(k).contains(e) implies self@.to_set().contains(e) by
                {
                    assert(old(self)@.to_set().contains(e));
                    assert(self@.to_set().contains(e)) by {
                        assert(self@.contains(e)) by {
                            let ind = choose |i| 0 <= i < old(self)@.len() && old(self)@[i] == e;
                            assert(ind != i);
                            if ind < i {
                                assert(self@[ind] == e);
                            } else if ind > i {
                                assert(self@[ind-1] == e);
                            }
                        };
                    };
                }

                assert forall |e| self@.to_set().contains(e) implies old(self)@.to_set().remove(k).contains(e) by 
                {
                }
            }

            /*
            let old_s = old(self)@.to_set().remove(k);
            let new_s = self@.to_set();
             {
                assert(old(self)@.to_set().contains(e));
                let n = choose |n: int| 0 <= n < old(self)@.len() && old(self)@[n] == e;
                if n < i {
                    assert(self@[n] == e);  // OBSERVE
                } else {
                    assert(self@[n-1] == e);  // OBSERVE
                }
            }
            assert_sets_equal!(self@.to_set(), old(self)@.to_set().remove(k));
            */
        }
        k
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
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

pub trait VerusClone : Sized {
}


}
