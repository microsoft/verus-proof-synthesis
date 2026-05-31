use vstd::prelude::*;

fn main() {}

verus!{

// File: kheap.rs
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KHeap {
    /// Maximum heap size in bytes (immutable after init).
    pub capacity: u32,
    /// Total bytes currently allocated.
    pub allocated_bytes: u32,
}

impl KHeap {

    pub open spec fn inv(&self) -> bool {
        &&& self.capacity > 0
        &&& self.allocated_bytes <= self.capacity
    }

	#[verifier::external_body]
    pub fn alloc(&mut self, bytes: u32) -> (rc: i32)
        requires
            old(self).inv(),
            bytes > 0,
        ensures
            self.inv(),
            self.capacity == old(self).capacity,
            // KH2: space available -> allocated
            old(self).allocated_bytes + bytes <= old(self).capacity ==> {
                &&& rc == OK
                &&& self.allocated_bytes == old(self).allocated_bytes + bytes
            },
            // KH3: would exceed capacity -> error, unchanged
            old(self).allocated_bytes + bytes > old(self).capacity ==> {
                &&& rc == ENOMEM
                &&& self.allocated_bytes == old(self).allocated_bytes
            },
	{
		unimplemented!()
	}

    pub fn calloc(&mut self, num: u32, size: u32) -> (rc: i32)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.capacity == old(self).capacity,
            // Overflow in multiplication -> error
            (num as u64) * (size as u64) > u32::MAX as u64 ==> {
                &&& rc == ENOMEM
                &&& self.allocated_bytes == old(self).allocated_bytes
            },
            // Zero-size allocation -> error
            num == 0 || size == 0 ==> {
                &&& rc == ENOMEM
                &&& self.allocated_bytes == old(self).allocated_bytes
            },
    {
        // Proof hint: u32 values cast to u64 have product <= u32::MAX^2 < u64::MAX.
        let num64: u64 = num as u64;
        let size64: u64 = size as u64;
        // Check for multiplication overflow (models size_mul_overflow)
        #[allow(clippy::arithmetic_side_effects)]
        let total: u64 = num64 * size64;
        if total == 0 || total > u32::MAX as u64 {
            return ENOMEM;
        }
        let total_u32: u32 = total as u32;
        self.alloc(total_u32)
    }

}



// File: error.rs
pub const ENOMEM: i32 = -12;

pub const OK: i32 = 0;


}
