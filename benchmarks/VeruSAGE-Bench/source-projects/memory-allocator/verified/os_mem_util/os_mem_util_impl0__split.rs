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


// File: os_mem_util.rs
impl MemChunk {

    pub proof fn split(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked t: Self)
        ensures
            t.points_to.dom() == old(self).points_to.dom().intersect(set_int_range(start, start + len)),
            t.os == old(self).os.restrict(set_int_range(start, start + len)),
            self.points_to.dom() == old(self).points_to.dom().difference(set_int_range(start, start + len)),
            self.os == old(self).os.remove_keys(set_int_range(start, start + len)),
            self.points_to.provenance() == old(self).points_to.provenance(),
            self.points_to.provenance() == t.points_to.provenance(),
    {
        let tracked split_os = self.os.tracked_remove_keys(
            set_int_range(start, start + len).intersect(self.os.dom())
        );

        let tracked mut pt = PointsToRaw::empty(self.points_to.provenance());
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked (rt, pt) = pt.split(set_int_range(start, start + len).intersect(pt.dom()));
        self.points_to = pt;

        let tracked t = MemChunk { os: split_os, points_to: rt };

        assert(self.points_to.dom() =~= old(self).points_to.dom().difference(set_int_range(start, start + len)));
        assert(self.os =~= old(self).os.remove_keys(set_int_range(start, start + len)));
        assert(t.points_to.dom() =~= old(self).points_to.dom().intersect(set_int_range(start, start + len)));
        assert(t.os =~= old(self).os.restrict(set_int_range(start, start + len)));

        t
    }

}



}
