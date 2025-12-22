use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;

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


// File: os_mem_util.rs
impl MemChunk {

    pub proof fn take_points_to_set(
        tracked &mut self,
        s: Set<int>,
    ) -> (tracked points_to: PointsToRaw)
        requires 
            s <= old(self).points_to.dom()
        ensures
            self.os == old(self).os,
            self.points_to.dom() == old(self).points_to.dom().difference(s),
            points_to.dom() == s,
            self.points_to.provenance() == old(self).points_to.provenance(),
            points_to.provenance() == old(self).points_to.provenance(),
    {
        let tracked mut pt = PointsToRaw::empty(self.points_to.provenance());
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked (rt, pt) = pt.split(s);
        self.points_to = pt;
        assert(rt.dom() =~= s);
        rt
    }

}



}
