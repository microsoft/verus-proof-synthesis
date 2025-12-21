use vstd::prelude::*;


fn main() {}

verus! {

pub const INTPTR_SIZE: u64 = 8;

pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

pub const MAX_ALIGN_SIZE: usize = 16;

pub const MAX_ALIGN_GUARANTEE: usize = 8 * MAX_ALIGN_SIZE;

pub closed spec fn start_offset(block_size: int) -> int {
    // Based on _mi_segment_page_start_from_slice
    if block_size >= INTPTR_SIZE as int && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    }
}

pub proof fn start_offset_le_slice_size(block_size: int)
    ensures 0 <= start_offset(block_size) <= SLICE_SIZE,
        start_offset(block_size) == 0 || start_offset(block_size) == 3 * MAX_ALIGN_GUARANTEE,
{
}

}
