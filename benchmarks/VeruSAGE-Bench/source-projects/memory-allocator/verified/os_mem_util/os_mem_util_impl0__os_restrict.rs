use vstd::prelude::*;
use vstd::raw_ptr::*;
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
    pub open spec fn range_os(&self) -> Set<int> {
        self.os.dom()
    }

    pub open spec fn os_has_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_os()
    }

}



// File: os_mem_util.rs
impl MemChunk {

    pub proof fn os_restrict(
        tracked &mut self,
        start: int,
        len: int
    )
        requires old(self).os_has_range(start, len),
        ensures self.points_to == old(self).points_to,
            self.os == old(self).os.restrict(set_int_range(start, start + len))
    {
        self.os.tracked_remove_keys(self.os.dom() - set_int_range(start, start + len));
        assert(self.os =~= old(self).os.restrict(set_int_range(start, start + len)));
    }

}



}
