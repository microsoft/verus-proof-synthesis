use vstd::prelude::*;

fn main() {}

verus!{


// Log of the (pointer-size in bytes) // TODO make configurable
pub const INTPTR_SHIFT: u64 = 3;
pub const INTPTR_SIZE: u64 = 8;
global size_of usize == 8;

// Log of the size of a 'slice'
pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

// Size of a slice
pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

// Log of the size of a 'segment'
pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

// Log of the size of a 'segment'
pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

// Log of the size of a 'segment'
pub const SEGMENT_ALIGN: u64 = SEGMENT_SIZE;

// Size of a 'segment'
pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const BIN_HUGE: u64 = 73;

// Fake bin that contains the "full" list. This is not a valid bin idx
// according to the valid_bin_idx spec in bin_sizes.rs.
pub const BIN_FULL: u64 = BIN_HUGE + 1;

pub const SMALL_PAGE_SHIFT: u64 = SLICE_SHIFT;
pub const MEDIUM_PAGE_SHIFT: u64 = 3 + SMALL_PAGE_SHIFT;

pub const SMALL_PAGE_SIZE: u64 = 1u64 << SMALL_PAGE_SHIFT;
pub const MEDIUM_PAGE_SIZE: u64 = 1u64 << MEDIUM_PAGE_SHIFT;

pub const SMALL_OBJ_SIZE_MAX: u64 = (SMALL_PAGE_SIZE / 4);
pub const MEDIUM_OBJ_SIZE_MAX: u64 = MEDIUM_PAGE_SIZE / 4;
pub const MEDIUM_OBJ_WSIZE_MAX: u64 = MEDIUM_OBJ_SIZE_MAX / (usize::BITS as u64 / 8);
pub const LARGE_OBJ_SIZE_MAX: u64 = (SEGMENT_SIZE / 2);

// maximum alloc size the user is allowed to request
// note: mimalloc use ptrdiff_t max here
pub const MAX_ALLOC_SIZE: usize = isize::MAX as usize;

pub const SMALL_WSIZE_MAX: usize = 128;
pub const PAGES_DIRECT: usize = SMALL_WSIZE_MAX + 1;
pub const SMALL_SIZE_MAX: usize = SMALL_WSIZE_MAX * INTPTR_SIZE as usize;

pub const MAX_ALIGN_SIZE: usize = 16;
pub const MAX_ALIGN_GUARANTEE: usize = 8 * MAX_ALIGN_SIZE;

pub const SEGMENT_BIN_MAX: usize = 31;

pub const ALIGNMENT_MAX: u64 = (SEGMENT_SIZE / 2);

pub const SIZEOF_SEGMENT_HEADER: usize = 264;
pub const SIZEOF_PAGE_HEADER: usize = 80;
pub const SIZEOF_HEAP: usize = 2904;
pub const SIZEOF_TLD: usize = 552;

// commit mask

pub const COMMIT_SIZE: u64 = SLICE_SIZE;
pub const COMMIT_MASK_BITS: u64 = SLICES_PER_SEGMENT;
pub const COMMIT_MASK_FIELD_COUNT: u64 = COMMIT_MASK_BITS / (usize::BITS as u64);

// huge 

pub const HUGE_BLOCK_SIZE: u32 = 0x80000000; // 2 GiB

// Helpers

pub proof fn const_facts()
    ensures SLICE_SIZE == 65536,
        SEGMENT_SIZE == 33554432,
        SLICES_PER_SEGMENT == 512,
        SMALL_PAGE_SIZE == 65536,
        MEDIUM_PAGE_SIZE == 524288,

        SMALL_OBJ_SIZE_MAX == 16384,
        MEDIUM_OBJ_SIZE_MAX == 131072,
        MEDIUM_OBJ_WSIZE_MAX == 16384,
        SMALL_SIZE_MAX == 1024,
        LARGE_OBJ_SIZE_MAX == 16777216,

        COMMIT_MASK_FIELD_COUNT == 8,

{
    
}
}
