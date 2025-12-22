use vstd::prelude::*;

fn main(){}

verus! {

pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::new(|i: nat| lo <= i && i < hi)
}

pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).finite(),
        set_nat_range(lo, hi).len() == hi - lo,
    decreases
        hi - lo,
{
    if lo == hi {
        assert(set_nat_range(lo, hi) =~= Set::empty());
    } else {
        lemma_nat_range(lo, (hi - 1) as nat);
        assert(set_nat_range(lo, (hi - 1) as nat).insert((hi - 1) as nat) =~= set_nat_range(lo, hi));
    }
}

}
