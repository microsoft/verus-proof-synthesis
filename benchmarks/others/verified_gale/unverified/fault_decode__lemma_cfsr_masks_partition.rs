use vstd::prelude::*;

fn main() {}

verus!{

// File: fault_decode.rs
pub const MMFSR_MASK: u32 = 0x0000_00FFu32;

pub const BFSR_MASK: u32  = 0x0000_FF00u32;

pub const UFSR_MASK: u32  = 0xFFFF_0000u32;

pub proof fn lemma_cfsr_masks_partition()
    ensures
        // Non-overlapping
        (MMFSR_MASK & BFSR_MASK) == 0,
        (MMFSR_MASK & UFSR_MASK) == 0,
        (BFSR_MASK  & UFSR_MASK) == 0,
        // Complete coverage
        (MMFSR_MASK | BFSR_MASK | UFSR_MASK) == 0xFFFF_FFFFu32,
{
}


}
