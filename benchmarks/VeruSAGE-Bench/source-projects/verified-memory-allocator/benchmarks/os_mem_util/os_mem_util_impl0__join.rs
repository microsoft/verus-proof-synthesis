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

    pub proof fn join(
        tracked &mut self,
        tracked t: Self,
    )
        requires
            old(self).points_to.provenance() == t.points_to.provenance(),
        ensures
            self.points_to.dom() == old(self).points_to.dom().union(t.points_to.dom()),
            self.os == old(self).os.union_prefer_right(t.os),
            self.points_to.provenance() == old(self).points_to.provenance(),
    {
        let tracked MemChunk { os, points_to } = t;
        self.os.tracked_union_prefer_right(os);

        let tracked mut pt = PointsToRaw::empty(Provenance::null());
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked pt = pt.join(points_to);
        self.points_to = pt;
    }

}



}
