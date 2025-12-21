use vstd::prelude::*;

fn main() {}

verus!{
proof fn element_outside_set(s: Set<nat>) -> (r: nat)
    requires
        s.finite(),
    ensures
        !s.contains(r),
{
    arbitrary() //TODO - replace with correct return value and proof
}
}
