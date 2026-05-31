use vstd::prelude::*;

fn main() {}

verus!{

// File: atomic.rs
pub proof fn lemma_or_idempotent(a: u32, b: u32)
    ensures
        (a | b) | b == (a | b),
{
}


}
