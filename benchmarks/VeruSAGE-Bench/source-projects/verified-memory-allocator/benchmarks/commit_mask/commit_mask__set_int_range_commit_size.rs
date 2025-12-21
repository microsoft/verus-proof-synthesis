use vstd::prelude::*;
use vstd::set_lib::set_int_range;
use vstd::raw_ptr::*;


fn main(){}


verus! {

uninterp spec fn is_bit_set(a: usize, b: usize) -> bool;

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

impl CommitMask {

    pub closed spec fn view(&self) -> Set<int> {
        Set::new(|t: (int, usize)|
                 0 <= t.0 < 8 && t.1 < 64
                 && is_bit_set(self.mask[t.0], t.1)
        ).map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    #[verifier::opaque]
    pub open spec fn bytes(&self, segment_id: SegmentId) -> Set<int> {
        Set::<int>::new(|addr: int|
            self@.contains(
                (addr - segment_start(segment_id)) / COMMIT_SIZE as int
            )
        )
    }
}

pub proof fn set_int_range_commit_size(sid: SegmentId, mask: CommitMask)
    requires mask@.contains(0)
    ensures set_int_range(segment_start(sid), segment_start(sid) + COMMIT_SIZE) <= mask.bytes(sid)
{
    reveal(CommitMask::bytes);
}


pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

pub const COMMIT_SIZE: u64 = SLICE_SIZE;


	#[verifier::external_body]
pub closed spec fn segment_start(segment_id: SegmentId) -> int
	{
		unimplemented!()
	}

pub ghost struct SegmentId {
    pub id: nat,
    pub provenance: Provenance,
    pub uniq: int,
}

}
