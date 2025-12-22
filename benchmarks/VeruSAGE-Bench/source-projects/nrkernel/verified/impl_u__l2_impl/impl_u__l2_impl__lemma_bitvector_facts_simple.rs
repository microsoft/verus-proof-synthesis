use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

macro_rules! bit {
    ($v:expr) => {
        1usize << $v
    }
}

pub(crate) use bit;


// File: spec_t/mmu/translation.rs
pub const MASK_DIRTY_ACCESS: usize = bit!(5) | bit!(6);

pub const MASK_NEG_DIRTY_ACCESS: usize = !MASK_DIRTY_ACCESS;


// File: impl_u/l2_impl.rs
#[verifier::spinoff_prover]
pub proof fn lemma_bitvector_facts_simple()
    ensures
        bit!(0usize) == 1,
        0 & MASK_NEG_DIRTY_ACCESS == 0,
        1usize << 0 == 1,
        0usize & 1 == 0,
{
    assert(bit!(0usize) == 1) by (bit_vector);
    assert(0 & !(bit!(5) | bit!(6)) == 0) by (bit_vector);
    assert(1usize << 0 == 1) by (bit_vector);
    assert(0usize & 1 == 0) by (bit_vector);
}


}
