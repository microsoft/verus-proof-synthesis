use vstd::prelude::*;

fn main() {}

verus!{

// File: fault_decode.rs
pub const HFSR_FORCED: u32   = 1u32 << 30u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CortexMFault {
    /// Configurable Fault Status Register (SCB->CFSR).
    /// Contains MMFSR (bits 0-7), BFSR (bits 8-15), UFSR (bits 16-31).
    pub cfsr: u32,
    /// HardFault Status Register (SCB->HFSR).
    pub hfsr: u32,
    /// MemManage Fault Address Register (SCB->MMFAR).
    /// Valid only when MMFSR.MMARVALID is set.
    pub mmfar: u32,
    /// BusFault Address Register (SCB->BFAR).
    /// Valid only when BFSR.BFARVALID is set.
    pub bfar: u32,
}

pub proof fn lemma_forced_is_hardfault()
    ensures ({
        let f = CortexMFault { cfsr: 0, hfsr: HFSR_FORCED, mmfar: 0, bfar: 0 };
        (f.hfsr & HFSR_FORCED) != 0
    })
{
    assert(((1u32 << 30u32) & (1u32 << 30u32)) != 0u32) by (bit_vector);
}


}
