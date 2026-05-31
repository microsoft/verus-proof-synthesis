use vstd::prelude::*;

fn main() {}

verus!{

// File: fault_decode.rs
pub const HFSR_VECTTBL: u32  = 1u32 << 1u32;

pub const HFSR_FORCED: u32   = 1u32 << 30u32;

pub const HFSR_DEBUGEVT: u32 = 1u32 << 31u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaultCategory {
    /// MemManage fault (MPU violation, stack guard hit).
    MemManage,
    /// Bus fault (invalid memory access on bus).
    BusFault,
    /// Usage fault (illegal instruction, alignment, etc.).
    UsageFault,
    /// Hard fault (escalated or vector table fault).
    HardFault,
    /// No fault detected (all status bits clear).
    None,
}

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

impl CortexMFault {

    pub open spec fn inv(&self) -> bool {
        true
    }

    pub fn classify(&self) -> (result: FaultCategory)
        requires self.inv(),
        ensures
            // FH3: if FORCED is set, it's a HardFault
            (self.hfsr & HFSR_FORCED) != 0
                ==> result === FaultCategory::HardFault,
            (self.hfsr & HFSR_VECTTBL) != 0
                ==> result === FaultCategory::HardFault,
            // U-3 fix: DEBUGEVT (bit 31) also escalates to HardFault per the
            // ARMv7-M architecture reference — a debug-monitor fault that
            // couldn't be handled by the DebugMon handler re-enters as
            // HardFault with HFSR.DEBUGEVT=1. Previously this class was
            // silently classified as None and execution continued.
            (self.hfsr & HFSR_DEBUGEVT) != 0
                ==> result === FaultCategory::HardFault,
            // FH1: if no HFSR bits but MMFSR bits set, it's MemManage
            (self.hfsr & (HFSR_FORCED | HFSR_VECTTBL | HFSR_DEBUGEVT)) == 0
                && (self.cfsr & 0x0000_00FFu32) != 0
                ==> result === FaultCategory::MemManage,
            // FH1: if no HFSR/MMFSR bits but BFSR bits set, it's BusFault
            (self.hfsr & (HFSR_FORCED | HFSR_VECTTBL | HFSR_DEBUGEVT)) == 0
                && (self.cfsr & 0x0000_00FFu32) == 0
                && (self.cfsr & 0x0000_FF00u32) != 0
                ==> result === FaultCategory::BusFault,
            // FH1: remaining CFSR bits -> UsageFault
            (self.hfsr & (HFSR_FORCED | HFSR_VECTTBL | HFSR_DEBUGEVT)) == 0
                && (self.cfsr & 0x0000_00FFu32) == 0
                && (self.cfsr & 0x0000_FF00u32) == 0
                && (self.cfsr & 0xFFFF_0000u32) != 0
                ==> result === FaultCategory::UsageFault,
            // All clear -> None
            (self.hfsr & (HFSR_FORCED | HFSR_VECTTBL | HFSR_DEBUGEVT)) == 0
                && self.cfsr == 0
                ==> result === FaultCategory::None,
    {
        let hfsr = self.hfsr;
        let cfsr = self.cfsr;

        // Check HardFault first (highest priority)
        if (hfsr & HFSR_FORCED) != 0
            || (hfsr & HFSR_VECTTBL) != 0
            || (hfsr & HFSR_DEBUGEVT) != 0
        {
            FaultCategory::HardFault
        }
        // Check MemManage (CFSR bits 0-7)
        else if (cfsr & 0x0000_00FFu32) != 0 {
            FaultCategory::MemManage
        }
        // Check BusFault (CFSR bits 8-15)
        else if (cfsr & 0x0000_FF00u32) != 0 {
            FaultCategory::BusFault
        }
        // Check UsageFault (CFSR bits 16-31)
        else if (cfsr & 0xFFFF_0000u32) != 0 {
            FaultCategory::UsageFault
        }
        // No fault detected
        else {
            FaultCategory::None
        }
    }

}

}
