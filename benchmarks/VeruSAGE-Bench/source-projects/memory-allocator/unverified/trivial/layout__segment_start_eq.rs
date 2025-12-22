use vstd::prelude::*;

use vstd::raw_ptr::*;

fn main() {}


verus! {

/*
Definitions from vstd
-----
vstd::raw_ptr
-----
#[verifier::external_body]
pub ghost struct Provenance {}

impl Provenance {
    pub uninterp spec fn null() -> Self;
}
-----
*/

pub const INTPTR_SHIFT: u64 = 3;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub ghost struct SegmentId {
    pub id: nat,
    pub provenance: Provenance,
    pub uniq: int,
}

pub closed spec fn segment_start(segment_id: SegmentId) -> int {
    segment_id.id * (SEGMENT_SIZE as int)
}

pub proof fn segment_start_eq(sid: SegmentId, sid2: SegmentId)
    requires sid.id == sid2.id,
    ensures segment_start(sid) == segment_start(sid2)
{
}

}
