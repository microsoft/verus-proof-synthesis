use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}


// File: extra.rs
	#[verifier::external_body]
pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) 
    requires aligned(a, b * c), b > 0, c > 0
    ensures aligned(a, b)
	{
		unimplemented!()
	}


// File: impl_u/indexing.rs
pub open spec fn nat_mul(a: nat, b: nat) -> nat {
    a * b
}

pub proof fn lemma_entry_base_from_index_support(base: nat, idx: nat, entry_size: nat)
    requires entry_size > 0
    ensures
        forall|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b),
        forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a),
        forall|a: nat| #[trigger] aligned(base, nat_mul(entry_size, a)) && a > 0 ==> aligned(base, entry_size),
{
    assert(forall|a: nat, b: nat| nat_mul(a, b) == #[trigger] (a * b)) by(nonlinear_arith);
    assert(forall|a: nat, b: nat| nat_mul(a, b) == nat_mul(b, a)) by(nonlinear_arith);
    assert forall|a: nat|
        #[trigger] aligned(base, nat_mul(entry_size, a)) && a > 0
        implies
        aligned(base, entry_size) by
    {
        mod_mult_zero_implies_mod_zero(base, entry_size, a);
    };
}


}
