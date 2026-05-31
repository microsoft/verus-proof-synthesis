use vstd::prelude::*;

fn main() {}

verus!{

// File: systick.rs
pub proof fn lemma_monotonicity(c1: u64, c2: u64, cycles_per_tick: u32)
    requires
        cycles_per_tick > 0,
        c1 <= c2,
    ensures
        (c1 as int) / (cycles_per_tick as int) <= (c2 as int) / (cycles_per_tick as int),
{
}


}
