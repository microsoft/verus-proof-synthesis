use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
pub proof fn leq_add_aligned_less(a: nat, b: nat, c: nat) 
    requires 0 < b, a < c, aligned(a, b), aligned(c, b),
    ensures a + b <= c,
{
    assert(a == b * (a / b) + a % b)by (nonlinear_arith)
        requires 0 < b, a < c, aligned(a, b), aligned(c, b);
    assert(c == b * (c / b) + c % b) by (nonlinear_arith)
        requires 0 < b, a < c, aligned(a, b), aligned(c, b);
    assert( a + b <= c) by (nonlinear_arith)
        requires 0 < b, a < c, aligned(a, b), aligned(c, b);

}


}
