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

    pub fn finish_cancel(&mut self)
        requires
            old(self).inv(),
            (old(self).flags & FLAG_CANCELING) != 0,
        ensures
            self.inv(),
            (self.flags & FLAG_CANCELING) == 0,
    {
        let old_flags = self.flags;
        #[allow(clippy::arithmetic_side_effects)]
        {
            self.flags = self.flags & !FLAG_CANCELING;
        }
        proof {
            assert(((old_flags & !2u8) & !(1u8 | 2u8 | 4u8 | 16u8)) == 0u8) by (bit_vector)
                requires (old_flags & !(1u8 | 2u8 | 4u8 | 16u8)) == 0u8;
            assert(((old_flags & !2u8) & 2u8) == 0u8) by (bit_vector);
        }
    }

}



}
