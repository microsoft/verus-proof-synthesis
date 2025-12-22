use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::layout::*;

fn main() {}

verus! {

pub open spec fn is_block_ptr(ptr: *mut u8, block_id: BlockId) -> bool {
    &&& ptr@.provenance == block_id.page_id.segment_id.provenance
    &&& ptr@.metadata == ()
    &&& is_block_ptr1(ptr as int, block_id)
}

	#[verifier::external_body]
pub open spec fn is_block_ptr1(ptr: int, block_id: BlockId) -> bool 
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn block_ptr_aligned_to_word()
    ensures forall |p, block_id| is_block_ptr(p, block_id) ==>
        p as int % align_of::<Node>() as int == 0
	{
		unimplemented!()
	}

pub proof fn is_block_ptr_mult4(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int % 4 == 0,
{
    hide(is_block_ptr);
    size_of_node();
    block_ptr_aligned_to_word();
}



pub struct Node {
    pub ptr: *mut Node,
}

	#[verifier::external_body]
pub proof fn size_of_node()
    ensures size_of::<Node>() == 8
        && align_of::<Node>() == 8
	{
		unimplemented!()
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
