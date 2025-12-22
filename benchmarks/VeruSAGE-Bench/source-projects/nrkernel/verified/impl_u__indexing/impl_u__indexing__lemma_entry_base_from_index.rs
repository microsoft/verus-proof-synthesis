use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}



// File: extra.rs
#[verifier::external_body]
pub proof fn mod_add_zero(a: nat, b: nat, c: nat)
    requires aligned(a, c), aligned(b, c), c > 0
    ensures aligned(a + b, c)
	{
		unimplemented!()
	}

#[verifier::external_body]
pub proof fn aligned_transitive(a: nat, b: nat, c: nat)
    requires
        0 < b,
        0 < c,
        aligned(a, b),
        aligned(b, c),
    ensures aligned(a, c)
	{
		unimplemented!()
	}

#[verifier::external_body]
pub proof fn mult_less_mono_both1(a: nat, b: nat, c: nat, d: nat)
    requires
        a < c,
        b <= d,
        0 < c,
        0 < d,
    ensures
        a * b < c * d
	{
		unimplemented!()
	}

// File: impl_u/indexing.rs
pub proof fn lemma_entry_base_from_index(base: nat, idx: nat, entry_size: nat)
    requires
        0 < entry_size,
    ensures
        entry_base_from_index(base, idx, entry_size) < next_entry_base_from_index(base, idx, entry_size),
        forall|idx2: nat|
            #![trigger entry_base_from_index(base, idx, entry_size), entry_base_from_index(base, idx2, entry_size)]
            idx < idx2 ==> entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size),
        forall|idx2: nat| idx < idx2
            ==> next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx + 1, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx, entry_size) + entry_size,
        next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(base, idx, entry_size),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n),
        aligned(base, entry_size) ==> aligned(entry_base_from_index(base, idx, entry_size), entry_size),
        base <= entry_base_from_index(base, idx, entry_size),
{
        assert forall|idx2: nat|
            idx < idx2
            implies entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size) by
        {
            assert(entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size))
                by(nonlinear_arith)
                requires
                    0 < entry_size,
                    idx < idx2,
            {
                mult_less_mono_both1(idx, entry_size, idx2, entry_size);
            };
        };
        assert forall|idx2: nat|
            idx < idx2
            implies next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size) by
        {
            assert(next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size))
                by(nonlinear_arith)
                requires
                    idx < idx2
            {
            };
        };
        assert(next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx + 1, entry_size));
        assert(next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx, entry_size) + entry_size) by(nonlinear_arith);
        assert(next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(base, idx, entry_size));
        assert forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n)
            implies #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n) by
        {
            assert(aligned(entry_base_from_index(base, idx, entry_size), n))
                by(nonlinear_arith)
                requires
                    0 < n,
                    0 < entry_size,
                    aligned(base, n),
                    aligned(entry_size, n)
            {
                assert(aligned(idx * entry_size, entry_size)) by {
                    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(idx as int, entry_size as int);
                };
                assert(aligned(idx * entry_size, n)) by {
                    aligned_transitive(idx * entry_size, entry_size, n);
                };
                assert(aligned(base + idx * entry_size, n)) by {
                    mod_add_zero(base, idx * entry_size, n);
                };
            };
        };
        assert forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n)
            implies #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n) by
        {
            assert(aligned(next_entry_base_from_index(base, idx, entry_size), n))
                by(nonlinear_arith)
                requires
                    0 < n,
                    0 < entry_size,
                    aligned(base, n),
                    aligned(entry_size, n)
            {
                assert(aligned((idx + 1) * entry_size, entry_size)) by {
                    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(idx as int + 1, entry_size as int);
                };
                assert(aligned((idx + 1) * entry_size, n)) by {
                    aligned_transitive((idx + 1) * entry_size, entry_size, n);
                };
                assert(aligned(base + (idx + 1) * entry_size, n)) by {
                    mod_add_zero(base, (idx + 1) * entry_size, n);
                };
            };
        };
        assert(aligned(base, entry_size) ==> aligned(entry_base_from_index(base, idx, entry_size), entry_size));
        assert(base <= entry_base_from_index(base, idx, entry_size));
}
}
