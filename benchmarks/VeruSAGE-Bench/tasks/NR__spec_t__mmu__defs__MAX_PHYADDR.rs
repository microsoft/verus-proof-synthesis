use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

// File: spec_t/mmu/defs.rs

// The maximum physical address width is between 32 and 52 bits.
#[verifier::external_body]
pub const MAX_PHYADDR_WIDTH: usize = 52;

#[verifier::external_body]
pub proof fn axiom_max_phyaddr_width_facts()
    ensures
        32 <= MAX_PHYADDR_WIDTH <= 52,
{
		unimplemented!()
}

pub spec const MAX_PHYADDR_SPEC: usize = ((1usize << MAX_PHYADDR_WIDTH) - 1usize) as usize;

pub fn MAX_PHYADDR() -> ( ret : usize)
    ensures ret == MAX_PHYADDR_SPEC 
{
    let r = (1usize << MAX_PHYADDR_WIDTH) - 1usize;
    r
}


}
