use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) 
    requires aligned(a, b * c), b > 0, c > 0
    ensures aligned(a, b)
{
}


}
