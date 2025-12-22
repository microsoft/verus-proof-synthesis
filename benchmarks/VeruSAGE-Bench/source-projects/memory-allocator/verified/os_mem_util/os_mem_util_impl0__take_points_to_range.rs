use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: os_mem.rs
#[verifier(external_body)]
#[verus::trusted]
pub tracked struct OsMem {
    no_copy: NoCopy,
}

#[verus::trusted]
pub tracked struct MemChunk {
    pub os: Map<int, OsMem>,
    pub points_to: PointsToRaw,
}

impl MemChunk {

    #[verifier::inline]
    pub open spec fn range_points_to(&self) -> Set<int> {
        self.points_to.dom()
    }

}



// File: os_mem_util.rs
impl MemChunk {

    #[verifier::inline]
    pub open spec fn pointsto_has_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_points_to()
    }

    pub proof fn take_points_to_range(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked points_to: PointsToRaw)
        requires 
            len >= 0,
            old(self).pointsto_has_range(start, len),
        ensures
            self.os == old(self).os,
            self.points_to.dom() == old(self).points_to.dom().difference(set_int_range(start, start+len)),
            self.points_to.provenance() == old(self).points_to.provenance(),
            points_to.is_range(start, len),
            points_to.provenance() == old(self).points_to.provenance(),

    {
        let tracked mut pt = PointsToRaw::empty(self.points_to.provenance());
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked (rt, pt) = pt.split(set_int_range(start, start + len));
        self.points_to = pt;
        rt
    }

}



}
