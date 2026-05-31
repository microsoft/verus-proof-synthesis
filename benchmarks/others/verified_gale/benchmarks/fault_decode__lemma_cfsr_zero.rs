use vstd::prelude::*;

fn main() {}

verus!{

// File: fault_decode.rs
proof fn lemma_cfsr_zero(cfsr: u32)
    requires
        cfsr & 0x0000_00FFu32 == 0,
        cfsr & 0x0000_FF00u32 == 0,
        cfsr & 0xFFFF_0000u32 == 0,
    ensures
        cfsr == 0,
{
    assert(cfsr == 0u32) by (bit_vector)
        requires
            cfsr & 0x0000_00FFu32 == 0u32,
            cfsr & 0x0000_FF00u32 == 0u32,
            cfsr & 0xFFFF_0000u32 == 0u32;
}


}
