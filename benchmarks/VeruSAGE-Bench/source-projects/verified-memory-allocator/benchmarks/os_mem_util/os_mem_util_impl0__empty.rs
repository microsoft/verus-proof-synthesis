use vstd::prelude::*;
use vstd::raw_ptr::*;

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

    #[verifier::spinoff_prover]
    pub proof fn empty() -> (tracked mc: MemChunk)
    {
       MemChunk { os: Map::tracked_empty(), points_to: PointsToRaw::empty(Provenance::null()) }
    }

}



}
