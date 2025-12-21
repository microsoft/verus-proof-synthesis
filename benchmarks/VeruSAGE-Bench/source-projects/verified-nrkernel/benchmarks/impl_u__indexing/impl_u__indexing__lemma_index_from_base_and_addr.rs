use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec fn index_from_offset(offset: nat, entry_size: nat) -> (res: nat)
    recommends entry_size > 0,
{
    offset / entry_size
}

pub open spec fn index_from_base_and_addr(base: nat, addr: nat, entry_size: nat) -> nat
    recommends
        addr >= base,
        entry_size > 0,
{
    index_from_offset(sub(addr, base), entry_size)
}

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

pub open spec fn between(x: nat, a: nat, b: nat) -> bool {
    a <= x && x < b
}


// File: extra.rs
	#[verifier::external_body]
pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat)
    requires aligned(a, c), aligned(b, c), a <= b, c > 0
    ensures aligned((b - a) as nat, c)
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn div_mul_cancel(a: nat, b: nat) {
    requires([
             aligned(a, b),
             b != 0
    ]);
    ensures(a / b * b == a);
}

// File: impl_u/indexing.rs
pub proof fn lemma_index_from_base_and_addr(base: nat, addr: nat, entry_size: nat, num_entries: nat)
    requires
        addr >= base,
        addr < entry_base_from_index(base, num_entries, entry_size),
        entry_size > 0,
    ensures
        ({
            let idx = index_from_base_and_addr(base, addr, entry_size);
            &&& idx < num_entries
            &&& between(addr, entry_base_from_index(base, idx, entry_size), next_entry_base_from_index(base, idx, entry_size))
            &&& aligned(base, entry_size) && aligned(addr, entry_size) ==> addr == entry_base_from_index(base, idx, entry_size)
        }),
{
    let idx = index_from_base_and_addr(base, addr, entry_size);
    assert(idx < num_entries) by(nonlinear_arith)
        requires
            addr >= base,
            addr < entry_base_from_index(base, num_entries, entry_size),
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    { };
    assert(between(addr, entry_base_from_index(base, idx, entry_size), next_entry_base_from_index(base, idx, entry_size))) by(nonlinear_arith)
        requires
            addr >= base,
            addr < entry_base_from_index(base, num_entries, entry_size),
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    { };
    assert(aligned(base, entry_size) && aligned(addr, entry_size) ==> addr == entry_base_from_index(base, idx, entry_size)) by(nonlinear_arith)
        requires
            addr >= base,
            entry_size > 0,
            idx == index_from_offset(sub(addr, base), entry_size),
    {
        if aligned(base, entry_size) && aligned(addr, entry_size) {
            subtract_mod_eq_zero(base, addr, entry_size);
            div_mul_cancel(sub(addr, base), entry_size);
        }
    };
}
}
