use vstd::prelude::*;

fn main() {}

verus!{

// File: work.rs
pub const FLAG_RUNNING: u8 = 1;    // BIT(0)

pub const FLAG_CANCELING: u8 = 2;  // BIT(1)

pub const FLAG_QUEUED: u8 = 4;     // BIT(2)

pub const FLAG_FLUSHING: u8 = 16;  // BIT(4)

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkItem {
    /// State flags (RUNNING, CANCELING, QUEUED, FLUSHING).
    pub flags: u8,
}

impl WorkItem {

    pub open spec fn inv(&self) -> bool {
        // Only bits 0,1,2,4 may be set
        (self.flags & !( FLAG_RUNNING | FLAG_CANCELING | FLAG_QUEUED | FLAG_FLUSHING )) == 0
    }

    pub fn submit(&mut self) -> (result: i32)
        requires old(self).inv(),
        ensures
            self.inv(),
            // WK3: canceling -> rejected, unchanged
            (old(self).flags & FLAG_CANCELING) != 0 ==> {
                &&& result == EBUSY
                &&& self.flags == old(self).flags
            },
            // WK4: already queued -> no-op
            ((old(self).flags & FLAG_CANCELING) == 0 && (old(self).flags & FLAG_QUEUED) != 0) ==> {
                &&& result == 0
                &&& self.flags == old(self).flags
            },
    {
        if (self.flags & FLAG_CANCELING) != 0 {
            return EBUSY;
        }
        if (self.flags & FLAG_QUEUED) != 0 {
            // Already queued
            return 0;
        }
        // Not queued — queue it
        let was_running = (self.flags & FLAG_RUNNING) != 0;
        let old_flags = self.flags;
        #[allow(clippy::arithmetic_side_effects)]
        {
            self.flags = self.flags | FLAG_QUEUED;
        }
        proof {
            assert(((old_flags | 4u8) & !(1u8 | 2u8 | 4u8 | 16u8)) == 0u8) by (bit_vector)
                requires (old_flags & !(1u8 | 2u8 | 4u8 | 16u8)) == 0u8;
        }
        if was_running { 2 } else { 1 }
    }

}



// File: error.rs
pub const EBUSY: i32 = -16;


}
