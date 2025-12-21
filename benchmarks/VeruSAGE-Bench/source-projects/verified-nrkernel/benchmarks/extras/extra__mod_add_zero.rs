use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
#[verifier::spinoff_prover]
pub proof fn mod_add_zero(a: nat, b: nat, c: nat)
    requires aligned(a, c), aligned(b, c), c > 0
    ensures aligned(a + b, c)
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int, b as int, c as int);
    assert(0nat % c == (a + b) % c);
}


}
