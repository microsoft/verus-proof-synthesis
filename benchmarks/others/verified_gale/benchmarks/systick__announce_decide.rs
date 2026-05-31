use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_remainder_lower;

fn main() {}

verus!{

// File: systick.rs
#[derive(Debug)]
pub struct AnnounceDecideResult {
    /// Number of complete ticks to announce to the kernel.
    pub dticks: u32,
    /// New cycle_count value.
    pub new_cycle_count: u64,
    /// New announced_cycles value.
    pub new_announced_cycles: u64,
}

pub fn announce_decide(
    cycle_count: u64,
    announced_cycles: u64,
    overflow_cyc: u32,
    cycles_per_tick: u32,
) -> (result: Option<AnnounceDecideResult>)
    requires
        cycles_per_tick > 0,
        cycle_count as int + overflow_cyc as int <= u64::MAX as int,
        announced_cycles <= cycle_count + overflow_cyc as u64,
    ensures
        result.is_some() ==> {
            &&& result.unwrap().new_cycle_count as int == cycle_count as int + overflow_cyc as int
            &&& result.unwrap().dticks as int ==
                    (result.unwrap().new_cycle_count as int - announced_cycles as int)
                    / (cycles_per_tick as int)
        },
{
    // new_cc no-overflow: guaranteed by requires cycle_count + overflow_cyc <= u64::MAX.
    let new_cc = cycle_count + overflow_cyc as u64;
    // dcycles no-underflow: announced_cycles <= new_cc by requires.
    let dcycles = new_cc - announced_cycles;
    let cpt = cycles_per_tick as u64;
    let dticks = dcycles / cpt;
    // announced_add = dticks * cpt <= dcycles (integer division property).
    // By lemma_remainder_lower: dcycles >= (dcycles / cpt) * cpt = dticks * cpt.
    proof {
        lemma_remainder_lower(dcycles as int, cpt as int);
        assert(dticks as int * cpt as int <= dcycles as int);
    }
    let announced_add = dticks * cpt;
    // new_announced no-overflow:
    //   announced_cycles + announced_add
    //   <= announced_cycles + dcycles
    //   == announced_cycles + (new_cc - announced_cycles)
    //   == new_cc  <= u64::MAX.
    proof {
        assert(announced_add as int <= dcycles as int);
        assert(dcycles as int == new_cc as int - announced_cycles as int);
        assert(announced_cycles as int + announced_add as int <= u64::MAX as int);
    }
    let new_announced = announced_cycles + announced_add;
    // Truncate dticks to u32 — in practice always fits because
    // dcycles <= COUNTER_MAX * (number of wraps since last announce),
    // and Zephyr's ISR runs frequently enough.
    if dticks > u32::MAX as u64 {
        None
    } else {
        Some(AnnounceDecideResult {
            dticks: dticks as u32,
            new_cycle_count: new_cc,
            new_announced_cycles: new_announced,
        })
    }
}


}
