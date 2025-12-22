use vstd::prelude::*;
use vstd::{
    seq_lib::*, set_lib::*,
    *,
};

fn main() {}

verus! {

type ID = EndPoint;

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
        let ghost mut deleted_set;
        proof {
            deleted_set = Set::empty();
            assert_seqs_equal!(self@,
                               old(self)@.subrange(0, start as int) +
                               old(self)@.subrange(start as int + deleted as int,
                                                   old(self)@.len() as int));
            assert_sets_equal!(deleted_set,
                               old(self)@.subrange(start as int,
                                                   start as int + deleted as int).to_set());
            assert_sets_equal!(old(self)@.to_set(),
                               self@.to_set() + deleted_set);
        }
        while deleted < end - start
            invariant
                start <= end <= old(self)@.len(),
                self@.len() == old(self)@.len() - deleted,
                0 <= deleted <= end - start,
                old(self).valid(),
                self.valid(),
                self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int),
                deleted_set == old(self)@.subrange(start as int, start as int + deleted as int).to_set(),
                deleted_set.len() == deleted,
                old(self)@.to_set() == self@.to_set() + deleted_set,
            decreases
                end - start - deleted,
        {
            let ghost mut old_deleted_set;
            let ghost mut old_deleted_seq;
            let ghost mut target;
            proof {
                old_deleted_set = deleted_set;
                old_deleted_seq = old(self)@.subrange(start as int, start as int + deleted as int);
                target = self@[start as int];
                deleted_set = deleted_set.insert(self@[start as int]);
            }
            self.remove(start);
            deleted = deleted + 1;
            proof {
                assert_seqs_equal!(self@,
                                   old(self)@.subrange(0, start as int) +
                                   old(self)@.subrange(start as int + deleted as int,
                                                       old(self)@.len() as int));
                let deleted_seq = old(self)@.subrange(start as int,
                                                      start as int + deleted as int);
                seq_to_set_is_finite::<K>(deleted_seq);
                deleted_seq.unique_seq_to_set();

                assert forall |e| #[trigger] deleted_set.contains(e)
                                  implies deleted_seq.to_set().contains(e) by {
                    if e == target {
                        assert(deleted_seq[deleted as int - 1] == e); // OBSERVE
                    } else {
                        assert(old_deleted_set.contains(e));
                        assert(old_deleted_seq.contains(e));
                        let i = choose |i| 0 <= i < old_deleted_seq.len() && old_deleted_seq[i] == e;
                        assert(deleted_seq[i] == e); // OBSERVE
                    }
                }
                assert forall |e| #[trigger] deleted_seq.to_set().contains(e)
                                  implies deleted_set.contains(e)  by {
                    if e == target {
                    } else {
                        let i = choose |i| 0 <= i < deleted_seq.len() && deleted_seq[i] == e;
                        assert(old_deleted_seq[i] == e);    // OBSERVE
                    }
                }
                assert_sets_equal!(deleted_set,
                                   deleted_seq.to_set());
                assert_sets_equal!(old(self)@.to_set(),
                                   self@.to_set() + deleted_set);
            }
        }

    }
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
}


}
