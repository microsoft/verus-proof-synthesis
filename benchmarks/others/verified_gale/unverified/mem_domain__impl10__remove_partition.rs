use vstd::prelude::*;

fn main() {}

verus!{

// File: mem_domain.rs
pub const MAX_PARTITIONS: u32 = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemPartition {
    /// Start address of the partition.
    pub start: u32,
    /// Size in bytes (must be > 0 for active partitions).
    pub size: u32,
    /// Memory attributes (rwx flags, architecture-specific).
    pub attr: u32,
}

#[derive(Debug, Clone, Copy)]
pub struct MemDomain {
    /// Partition slots. A slot with size == 0 is free.
    pub partitions: [MemPartition; 16],
    /// Number of active (non-zero-size) partitions.
    pub num_partitions: u32,
}

impl MemPartition {

    pub open spec fn is_valid(&self) -> bool {
        self.size > 0
        && self.start as u64 + self.size as u64 <= u32::MAX as u64
    }

    pub open spec fn end_spec(&self) -> int {
        self.start as u64 + self.size as u64
    }

    pub open spec fn overlaps_spec(&self, other: &MemPartition) -> bool {
        self.end_spec() > other.start as u64
        && other.end_spec() > self.start as u64
    }

}


impl MemDomain {

    pub open spec fn inv(&self) -> bool {
        // MD4: bounded count
        &&& self.num_partitions <= MAX_PARTITIONS
        // MD3 + MD6: all active partitions are valid
        &&& forall|i: int| 0 <= i < MAX_PARTITIONS as int
            ==> (#[trigger] self.partitions[i]).size > 0
            ==> self.partitions[i].is_valid()
        // MD1: no two active partitions overlap
        &&& forall|i: int, j: int|
            0 <= i < MAX_PARTITIONS as int
            && 0 <= j < MAX_PARTITIONS as int
            && i != j
            && (#[trigger] self.partitions[i]).size > 0
            && (#[trigger] self.partitions[j]).size > 0
            ==> !self.partitions[i].overlaps_spec(&self.partitions[j])
    }

    pub fn remove_partition(&mut self, start: u32, size: u32) -> (result: Result<u32, i32>)
        requires
            old(self).inv(),
            old(self).num_partitions > 0,
        ensures
            self.inv(),
            // Success: partition cleared, count decremented
            result.is_ok() ==> {
                &&& self.num_partitions == old(self).num_partitions - 1
                &&& result.unwrap() < MAX_PARTITIONS
                &&& self.partitions[result.unwrap() as int].size == 0
            },
            // Error: state unchanged
            result.is_err() ==> {
                &&& self.num_partitions == old(self).num_partitions
                &&& forall|i: int| 0 <= i < MAX_PARTITIONS as int
                    ==> self.partitions[i] === old(self).partitions[i]
            },
    {
        // Find matching partition
        let orig_num = self.num_partitions;
        let mut p_idx: u32 = 0;
        while p_idx < MAX_PARTITIONS
        {
            if self.partitions[p_idx as usize].start == start
                && self.partitions[p_idx as usize].size == size
            {
                let slot = p_idx;

                // Clear the slot (size = 0 marks it as free)
                self.partitions[slot as usize] = MemPartition {
                    start: 0,
                    size: 0,
                    attr: 0,
                };

                self.num_partitions = self.num_partitions - 1;

                return Ok(slot);
            }
            p_idx = p_idx + 1;
        }

        Err(ENOENT)
    }

}



// File: error.rs
pub const ENOENT: i32 = -2;


}
