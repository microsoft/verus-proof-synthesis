use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_remainder;

fn main() {}

verus!{

// File: systick.rs
pub proof fn lemma_conversion_truncation(cycles: u64, cycles_per_tick: u32)
    requires
        cycles_per_tick > 0,
    ensures
        ({
            let ticks = (cycles as int) / (cycles_per_tick as int);
            let back = ticks * (cycles_per_tick as int);
            cycles as int - back < cycles_per_tick as int
        }),
{
    // Remainder after integer division: 0 <= a - (a/d)*d < d.
    // lemma_remainder(a, d) proves 0 <= a - a/d * d < d.
    lemma_remainder(cycles as int, cycles_per_tick as int);
}


}
