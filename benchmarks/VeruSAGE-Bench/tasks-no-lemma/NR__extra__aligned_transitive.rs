use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
pub proof fn aligned_transitive(a: nat, b: nat, c: nat)
    requires
        0 < b,
        0 < c,
        aligned(a, b),
        aligned(b, c),
    ensures aligned(a, c)
{
}


}
