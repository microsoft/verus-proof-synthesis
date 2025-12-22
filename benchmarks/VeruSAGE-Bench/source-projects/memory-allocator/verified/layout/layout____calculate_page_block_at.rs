use vstd::prelude::*;
use vstd::raw_ptr::*;

fn main () {}


verus! {

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

pub const INTPTR_SHIFT: u64 = 3;

pub const INTPTR_SIZE: u64 = 8;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const SMALL_PAGE_SHIFT: u64 = SLICE_SHIFT;

pub const MEDIUM_PAGE_SHIFT: u64 = 3 + SMALL_PAGE_SHIFT;

pub const SMALL_PAGE_SIZE: u64 = 1u64 << SMALL_PAGE_SHIFT;

pub const MEDIUM_PAGE_SIZE: u64 = 1u64 << MEDIUM_PAGE_SHIFT;

pub const SMALL_OBJ_SIZE_MAX: u64 = (SMALL_PAGE_SIZE / 4);

pub const MEDIUM_OBJ_SIZE_MAX: u64 = MEDIUM_PAGE_SIZE / 4;

pub const MEDIUM_OBJ_WSIZE_MAX: u64 = MEDIUM_OBJ_SIZE_MAX / (usize::BITS as u64 / 8);

pub const LARGE_OBJ_SIZE_MAX: u64 = (SEGMENT_SIZE / 2);

pub const SMALL_WSIZE_MAX: usize = 128;

pub const SMALL_SIZE_MAX: usize = SMALL_WSIZE_MAX * INTPTR_SIZE as usize;

pub const MAX_ALIGN_SIZE: usize = 16;

pub const MAX_ALIGN_GUARANTEE: usize = 8 * MAX_ALIGN_SIZE;

pub const SIZEOF_SEGMENT_HEADER: usize = 264;

pub const SIZEOF_PAGE_HEADER: usize = 80;

pub const SIZEOF_HEAP: usize = 2904;

pub const SIZEOF_TLD: usize = 552;

pub const COMMIT_MASK_BITS: u64 = SLICES_PER_SEGMENT;

pub const COMMIT_MASK_FIELD_COUNT: u64 = COMMIT_MASK_BITS / (usize::BITS as u64);

	#[verifier::external_body]
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

        /*
        vstd::layout::size_of::<SegmentHeader>() == SIZEOF_SEGMENT_HEADER,
        vstd::layout::size_of::<Page>() == SIZEOF_PAGE_HEADER,
        vstd::layout::size_of::<Heap>() == SIZEOF_HEAP,
        vstd::layout::size_of::<Tld>() == SIZEOF_TLD,

        vstd::layout::align_of::<SegmentHeader>() == 8,
        vstd::layout::align_of::<Page>() == 8,
        vstd::layout::align_of::<Heap>() == 8,
        vstd::layout::align_of::<Tld>() == 8,
        */
	{
		unimplemented!()
	}

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

pub fn calculate_page_block_at(
    page_start: usize,
    block_size: usize,
    idx: usize,
    Ghost(page_id): Ghost<PageId>
) -> (p: usize)
    requires page_start == block_start_at(page_id, block_size as int, 0),
        block_start_at(page_id, block_size as int, 0)
            + idx as int * block_size as int <= segment_start(page_id.segment_id) + SEGMENT_SIZE,
        segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX,
    ensures
        p == block_start_at(page_id, block_size as int, idx as int),
        p == page_start + idx as int * block_size as int
{
    proof {
        const_facts();
        assert(block_size * idx >= 0) by(nonlinear_arith)
            requires block_size >= 0, idx >= 0;
        assert(block_size * idx == idx * block_size) by(nonlinear_arith);
    }
    let p = page_start + block_size * idx;
    return p;
}


pub struct Node {
    pub ptr: *mut Node,
}

pub ghost struct HeapId {
    pub id: nat,
    pub provenance: Provenance,
    pub uniq: int,
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

}
