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
    let mmfsr_mask: u32 = MMFSR_MASK; //0x0000_00FFu32
    let bfsr_mask: u32 = BFSR_MASK; //0x0000_FF00u32;
    let ufsr_mask: u32 = UFSR_MASK; //0xFFFF_0000u32;

    assert((mmfsr_mask & bfsr_mask) == 0u32) by (bit_vector)
        requires
            mmfsr_mask == 0x0000_00FFu32,
            bfsr_mask == 0x0000_ff00u32,
        ;
    assert((mmfsr_mask & ufsr_mask) == 0u32) by (bit_vector)
        requires
            mmfsr_mask == 0x0000_00ffu32,
            ufsr_mask == 0xffff_0000u32,
        ;
    assert((bfsr_mask  & ufsr_mask) == 0u32) by (bit_vector)
        requires
            bfsr_mask == 0x0000_ff00u32,
            ufsr_mask == 0xffff_0000u32,
            ;
    assert((mmfsr_mask | bfsr_mask | ufsr_mask) == 0xFFFF_FFFFu32) by (bit_vector)
        requires
            mmfsr_mask == 0x0000_00FFu32,
            bfsr_mask == 0x0000_ff00u32,
            ufsr_mask == 0xffff_0000u32,
            ;
}


}
