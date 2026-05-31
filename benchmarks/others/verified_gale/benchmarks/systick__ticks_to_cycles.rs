use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_remainder_lower;
use vstd::arithmetic::mul::lemma_mul_inequality;

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
            // ticks <= u64::MAX / cpt  ==>  ticks * cpt <= u64::MAX.
            // By lemma_remainder_lower: u64::MAX >= (u64::MAX / cpt) * cpt.
            // By lemma_mul_inequality: ticks * cpt <= (u64::MAX / cpt) * cpt.
            proof {
                lemma_remainder_lower(u64::MAX as int, cpt as int);
                lemma_mul_inequality(ticks as int, u64::MAX as int / cpt as int, cpt as int);
                assert(ticks as int * cpt as int <= u64::MAX as int);
            }
            Some(ticks * cpt)
        }
    }
}


}
