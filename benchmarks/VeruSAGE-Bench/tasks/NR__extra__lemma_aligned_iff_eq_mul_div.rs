use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
pub proof fn lemma_aligned_iff_eq_mul_div(a: nat, b: nat)
    requires b > 0
    ensures aligned(a, b) <==> a == b * (a / b)
{

}


}
