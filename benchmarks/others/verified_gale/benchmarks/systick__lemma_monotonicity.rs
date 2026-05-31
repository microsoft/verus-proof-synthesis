use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_div_is_ordered;

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
    // Integer division is monotonic: a <= b ==> a/d <= b/d for d > 0.
    lemma_div_is_ordered(c1 as int, c2 as int, cycles_per_tick as int);
}


}
