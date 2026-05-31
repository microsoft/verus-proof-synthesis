use vstd::prelude::*;

fn main() {}

verus!{

// File: atomic.rs
pub proof fn lemma_xor_self_inverse(a: u32, b: u32)
    ensures
        (a ^ b) ^ b == a,
{
    assert((a ^ b) ^ b == a) by (bit_vector);
}


}
