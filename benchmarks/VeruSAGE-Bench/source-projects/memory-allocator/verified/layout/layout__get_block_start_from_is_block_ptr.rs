use vstd::prelude::*;
use vstd::raw_ptr::*;

fn main() {}

verus! {

pub const INTPTR_SHIFT: u64 = 3;

pub const INTPTR_SIZE: u64 = 8;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const MAX_ALIGN_SIZE: usize = 16;

pub const MAX_ALIGN_GUARANTEE: usize = 8 * MAX_ALIGN_SIZE;

pub closed spec fn segment_start(segment_id: SegmentId) -> int {
    segment_id.id * (SEGMENT_SIZE as int)
}

pub open spec fn page_start(page_id: PageId) -> int {
    segment_start(page_id.segment_id) + SLICE_SIZE * page_id.idx
}

pub closed spec fn start_offset(block_size: int) -> int {
    // Based on _mi_segment_page_start_from_slice
    if block_size >= INTPTR_SIZE as int && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    }
}

pub open spec fn block_start_at(page_id: PageId, block_size: int, block_idx: int) -> int {
    page_start(page_id)
         + start_offset(block_size)
         + block_idx * block_size
}

pub closed spec fn block_start(block_id: BlockId) -> int {
    block_start_at(block_id.page_id, block_id.block_size as int, block_id.idx as int)
}

pub open spec fn is_block_ptr(ptr: *mut u8, block_id: BlockId) -> bool {
    &&& ptr@.provenance == block_id.page_id.segment_id.provenance
    &&& ptr@.metadata == ()
    &&& is_block_ptr1(ptr as int, block_id)
}

#[verifier::opaque]
pub open spec fn is_block_ptr1(ptr: int, block_id: BlockId) -> bool {
    // ptr should be in the range (segment start, segment end]
    // Yes, that's open at the start and closed at the end
    //  - segment start is invalid since that's where the SegmentHeader is
    //  - segment end is valid because there might be a huge block there
    &&& segment_start(block_id.page_id.segment_id) < ptr
        <= segment_start(block_id.page_id.segment_id) + (SEGMENT_SIZE as int)
        < usize::MAX

    // Has valid slice_idx (again this is <= to account for the huge slice)
    &&& 0 <= block_id.slice_idx <= SLICES_PER_SEGMENT

    // It also has to be in the right slice
    &&& segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
        <= ptr
        < segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
              + SLICE_SIZE

    // the pptr should actually agree with the block_id
    &&& ptr == block_start(block_id)

    &&& 0 <= block_id.page_id.segment_id.id

    // The block size must be a multiple of the word size
    &&& block_id.block_size >= size_of::<Node>()
    &&& block_id.block_size % size_of::<Node>() as nat == 0
}

pub proof fn get_block_start_from_is_block_ptr(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int == block_start(block_id),
{
    reveal(is_block_ptr1);
}

pub struct Node {
    pub ptr: *mut Node,
}

pub ghost struct SegmentId {
    pub id: nat,
    pub provenance: Provenance,
    pub uniq: int,
}

pub ghost struct PageId {
    pub segment_id: SegmentId,
    pub idx: nat,
}

pub ghost struct BlockId {
    pub page_id: PageId,

    // Index of the block within the *page*
    pub idx: nat,

    // Recall that a page may be multiple slices.
    // The `slice_idx` is the index of the *specific* slice that this block is in.
    // (Relative to the segment, so the slice's "offset" is going to be
    // slice_idx - page_id.idx)
    pub slice_idx: nat,

    pub block_size: nat,
}

}
