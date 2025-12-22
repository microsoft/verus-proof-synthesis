use vstd::prelude::*;
use vstd::{
    seq_lib::*, set_lib::*,
    *,
};

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

	#[verifier::external_body]
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
		unimplemented!()
	}

    fn erase(&mut self, start: usize, end: usize)
        requires
            old(self).valid(),
            start <= end <= old(self)@.len(),
        ensures
            self.valid(),
            self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(end as int, old(self)@.len() as int),
            // TODO: We might want to strengthen this further to say that the two sets on the RHS
            //       are disjoint
            old(self)@.to_set() == self@.to_set() + old(self)@.subrange(start as int, end as int).to_set(),
    {
        let mut deleted = 0;

        proof {
            assert(self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int));
            assert(old(self)@.to_set() == self@.to_set() + old(self)@.subrange(start as int, start + deleted).to_set());
        }
        while deleted < end - start
            invariant
                start <= end <= old(self)@.len(),
                self@.len() == old(self)@.len() - deleted,
                0 <= deleted <= end - start,
                old(self).valid(),
                self.valid(),
                self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int),
                old(self)@.to_set() == self@.to_set() + old(self)@.subrange(start as int, start + deleted).to_set(),
            decreases
                end - start - deleted,
        {
            self.remove(start);
            deleted = deleted + 1;
            proof {
                assert(self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int));

                assert(old(self)@.to_set() == self@.to_set() + old(self)@.subrange(start as int, start + deleted).to_set()) by {
                    assert(old(self)@ =~= old(self)@.subrange(0, start as int) 
                                                + old(self)@.subrange(start as int, start + deleted)
                                                + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int));
                    seq_to_set_distributes_over_add::<K>(old(self)@.subrange(0, start as int), 
                                    old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int));
                    assert(old(self)@.to_set() =~= old(self)@.subrange(0, start as int).to_set()
                                                + old(self)@.subrange(start as int, start + deleted).to_set()
                                                + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int).to_set());
                    assert(self@.to_set() =~= old(self)@.subrange(0, start as int).to_set()
                                                + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int).to_set());

                    assert(old(self)@.to_set() =~= self@.to_set() + old(self)@.subrange(start as int, start + deleted).to_set());

 
                };

            }
        }

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

pub trait VerusClone : Sized {
    fn clone(&self) -> (o: Self)
        ensures o == self;  // this is way too restrictive; it kind of demands Copy. But we don't have a View trait yet. :v(
}


}
