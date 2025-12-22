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
pub ghost struct MemProtect {
    pub read: bool,
    pub write: bool,
}

#[verus::trusted]
pub ghost struct OsMemData {
    pub byte_addr: int,
    pub mem_protect: MemProtect,
}

#[verus::trusted]
pub tracked struct MemChunk {
    pub os: Map<int, OsMem>,
    pub points_to: PointsToRaw,
}

impl MemChunk {

    pub open spec fn wf(&self) -> bool {
        self.wf_os()
    }

    pub open spec fn wf_os(&self) -> bool {
        forall |addr: int|
            #[trigger] self.os.dom().contains(addr)
             ==> self.os[addr]@.byte_addr == addr
    }

}


impl OsMem {

    pub uninterp spec fn view(self) -> OsMemData;

}



// File: os_mem_util.rs
impl MemChunk {

    pub proof fn give_points_to_range(
        tracked &mut self,
        tracked points_to: PointsToRaw,
    )
        requires 
            old(self).wf(),
            old(self).points_to.provenance() == points_to.provenance()
        ensures
            self.wf(),
            self.os == old(self).os,
            self.points_to.dom() == old(self).points_to.dom() + points_to.dom(),
            self.points_to.provenance() == points_to.provenance(),
    {
        let tracked mut pt = PointsToRaw::empty(self.points_to.provenance());
        tracked_swap(&mut pt, &mut self.points_to);
        let tracked pt = pt.join(points_to);
        self.points_to = pt;
        assert(self.points_to.dom() =~= old(self).points_to.dom() + points_to.dom());
    }

}



}
