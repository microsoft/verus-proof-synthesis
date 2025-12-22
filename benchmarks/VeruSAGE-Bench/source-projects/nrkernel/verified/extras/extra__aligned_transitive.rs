use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
	#[verifier::external_body]
pub proof fn lemma_aligned_iff_eq_mul_div(a: nat, b: nat)
    requires b > 0
    ensures aligned(a, b) <==> a == b * (a / b)
	{
		unimplemented!()
	}

pub proof fn aligned_transitive(a: nat, b: nat, c: nat)
    requires
        0 < b,
        0 < c,
        aligned(a, b),
        aligned(b, c),
    ensures aligned(a, c)
{
    lemma_aligned_iff_eq_mul_div(a, b);
    lemma_aligned_iff_eq_mul_div(b, c);
    lemma_aligned_iff_eq_mul_div(a, c);
    let i = a / b; let j = b / c;
    assert((c * j) * i == c * (j * i)) by (nonlinear_arith);
    assert(a / c == j * i) by (nonlinear_arith)
        requires 0 < c, a == c * (j * i);
}


}
