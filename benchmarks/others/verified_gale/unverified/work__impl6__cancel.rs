use vstd::prelude::*;

fn main() {}

verus!{

// File: work.rs
pub const FLAG_RUNNING: u8 = 1;    // BIT(0)

pub const FLAG_CANCELING: u8 = 2;  // BIT(1)

pub const FLAG_QUEUED: u8 = 4;     // BIT(2)

pub const FLAG_FLUSHING: u8 = 16;  // BIT(4)

pub const BUSY_MASK: u8 = 7;       // 0b0000_0111

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

    pub fn cancel(&mut self) -> (result: u8)
        requires old(self).inv(),
        ensures
            self.inv(),
            // QUEUED is always cleared
            (self.flags & FLAG_QUEUED) == 0,
            result == (self.flags & BUSY_MASK),
    {
        let old_flags = self.flags;
        // Clear QUEUED
        #[allow(clippy::arithmetic_side_effects)]
        {
            self.flags = self.flags & !FLAG_QUEUED;
        }
        // If still busy (RUNNING), mark as CANCELING
        let busy = self.flags & BUSY_MASK;
        if busy != 0 {
            let mid_flags = self.flags;
            #[allow(clippy::arithmetic_side_effects)]
            {
                self.flags = self.flags | FLAG_CANCELING;
            }
        }
        self.flags & BUSY_MASK
    }

}



}
