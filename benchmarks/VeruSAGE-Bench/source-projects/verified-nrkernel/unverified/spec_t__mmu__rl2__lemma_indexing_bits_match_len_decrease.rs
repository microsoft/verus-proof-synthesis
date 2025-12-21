use vstd::prelude::*;

fn main() {}

verus!{

#[allow(unused_macros)]
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0usize << (($high+1usize)-$low))) << $low
    }
}

#[allow(unused_macros)]
macro_rules! l0_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(39usize,47usize)) >> 39usize }
}

#[allow(unused_macros)]
macro_rules! l1_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(30usize,38usize)) >> 30usize }
}

#[allow(unused_macros)]
macro_rules! l2_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(21usize,29usize)) >> 21usize }
}

#[allow(unused_macros)]
macro_rules! l3_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(12usize,20usize)) >> 12usize }
}

// File: spec_t/mmu/rl2.rs
// This file contains refinement layer 2 of the MMU. Compared to layer 3, it expresses translation
// caching and non-atomic walks as a single concept, and replaces the explicit havoc-ing of
// dirty/accessed bits with underspecified reads.

#[verifier(opaque)]
spec fn indexing_bits_match(va1: usize, va2: usize, len: nat) -> bool {
    &&& len > 0 ==> l0_bits!(va1) == l0_bits!(va2)
    &&& len > 1 ==> l1_bits!(va1) == l1_bits!(va2)
    &&& len > 2 ==> l2_bits!(va1) == l2_bits!(va2)
    &&& len > 3 ==> l3_bits!(va1) == l3_bits!(va2)
}

broadcast proof fn lemma_indexing_bits_match_len_decrease(va1: usize, va2: usize, len1: nat, len2: nat)
    requires
        #[trigger] indexing_bits_match(va1, va2, len1),
        len2 <= len1,
    ensures
        #[trigger] indexing_bits_match(va1, va2, len2),
{
}


}
