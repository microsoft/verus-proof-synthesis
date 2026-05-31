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

    pub fn has_free_slot(&self) -> (r: bool)
        requires self.inv(),
    {
        let mut i: u32 = 0;
        while i < MAX_PARTITIONS
            invariant
                0 <= i <= MAX_PARTITIONS,
            decreases MAX_PARTITIONS - i,
        {
            if self.partitions[i as usize].size == 0 {
                return true;
            }
            i = i + 1;
        }
        false
    }

}



}
