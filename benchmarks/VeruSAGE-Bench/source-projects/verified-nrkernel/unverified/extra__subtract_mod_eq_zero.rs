use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat)
    requires aligned(a, c), aligned(b, c), a <= b, c > 0
    ensures aligned((b - a) as nat, c)
{
}


}
