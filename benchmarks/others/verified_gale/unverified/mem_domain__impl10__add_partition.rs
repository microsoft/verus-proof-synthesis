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

	#[verifier::external_body]
    fn check_add_partition(&self, part: &MemPartition) -> (ok: bool)
        requires self.inv(),
        ensures
            ok ==> {
                &&& part.is_valid()
                &&& forall|i: int| 0 <= i < MAX_PARTITIONS as int
                    && (#[trigger] self.partitions[i]).size > 0
                    ==> !part.overlaps_spec(&self.partitions[i])
            },
	{
		unimplemented!()
	}

    pub fn add_partition(&mut self, part: &MemPartition) -> (result: Result<u32, i32>)
        requires
            old(self).inv(),
            old(self).num_partitions < MAX_PARTITIONS,
        ensures
            self.inv(),
            // Success: num_partitions incremented, slot index valid
            result.is_ok() ==> {
                &&& self.num_partitions == old(self).num_partitions + 1
                &&& result.unwrap() < MAX_PARTITIONS
            },
            // Error: state unchanged
            result.is_err() ==> self.num_partitions == old(self).num_partitions,
    {
        // Validate partition
        if !self.check_add_partition(part) {
            return Err(EINVAL);
        }

        // Save original num_partitions for the bound proof
        let ghost orig_partitions = self.partitions;
        let orig_num = self.num_partitions;

        // Find a free slot (size == 0)
        let mut p_idx: u32 = 0;
        while p_idx < MAX_PARTITIONS
        {
            if self.partitions[p_idx as usize].size == 0 {
                // Found a free slot — place partition here
                let slot = p_idx;

                self.partitions[slot as usize] = MemPartition {
                    start: part.start,
                    size: part.size,
                    attr: part.attr,
                };

                self.num_partitions = self.num_partitions + 1;

                return Ok(slot);
            }
            p_idx = p_idx + 1;
        }

        Err(ENOSPC)
    }

}



// File: error.rs
pub const EINVAL: i32 = -22;

pub const ENOSPC: i32 = -28;


}
