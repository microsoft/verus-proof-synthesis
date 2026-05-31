use vstd::prelude::*;

fn main() {}

verus!{

// File: fault_decode.rs
pub const HFSR_VECTTBL: u32  = 1u32 << 1u32;

pub const HFSR_FORCED: u32   = 1u32 << 30u32;

pub const HFSR_DEBUGEVT: u32 = 1u32 << 31u32;

proof fn lemma_hfsr_split(hfsr: u32)
    requires
        hfsr & HFSR_FORCED == 0,
        hfsr & HFSR_VECTTBL == 0,
        hfsr & HFSR_DEBUGEVT == 0,
    ensures
        (hfsr & (HFSR_FORCED | HFSR_VECTTBL | HFSR_DEBUGEVT)) == 0,
{
}


}
