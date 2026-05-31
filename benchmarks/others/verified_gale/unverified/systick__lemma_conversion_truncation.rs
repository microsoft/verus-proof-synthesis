use vstd::prelude::*;

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
}


}
