use vstd::prelude::*;

fn main() {}

verus!{

// File: systick.rs
pub fn ticks_to_cycles(ticks: u64, cycles_per_tick: u32) -> (result: Option<u64>)
    ensures
        cycles_per_tick == 0 ==> result === Some(0u64),
        cycles_per_tick > 0 && (ticks as int) > (u64::MAX as int) / (cycles_per_tick as int) ==>
            result.is_none(),
        cycles_per_tick > 0 && (ticks as int) <= (u64::MAX as int) / (cycles_per_tick as int) ==> {
            &&& result.is_some()
            &&& result.unwrap() as int == (ticks as int) * (cycles_per_tick as int)
        },
{
    if cycles_per_tick == 0 {
        // 0 cycles per tick => 0 cycles regardless of ticks
        Some(0u64)
    } else {
        let cpt = cycles_per_tick as u64;
        if ticks > u64::MAX / cpt {
            None
        } else {
            Some(ticks * cpt)
        }
    }
}


}
