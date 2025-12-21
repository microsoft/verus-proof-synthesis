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

pub const COMMIT_SIZE: u64 = SLICE_SIZE;


pub closed spec fn segment_start(segment_id: SegmentId) -> int {
    segment_id.id * (SEGMENT_SIZE as int)
}

pub proof fn segment_start_mult_commit_size(segment_id: SegmentId)
    ensures segment_start(segment_id) % COMMIT_SIZE as int == 0,
{
    assert(segment_start(segment_id) % COMMIT_SIZE as int == 0) by (compute);
}

pub ghost struct SegmentId {
    pub id: nat,
    pub provenance: Provenance,
    pub uniq: int,
}


}
