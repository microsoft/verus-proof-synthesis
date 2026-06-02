use vstd::prelude::*;


fn main() {}

verus! {

pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::new(|i: nat| lo <= i && i < hi)
}

proof fn nat_set_size(s:Set<nat>, bound:nat)
    requires
        forall |i: nat| (0 <= i < bound <==> s.contains(i)),
    ensures
        s.finite(),
        s.len() == bound,
{
}

}
