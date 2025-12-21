use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

// File: spec_t/mmu/defs.rs
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0usize << (($high+1usize)-$low))) << $low
    }
}

#[verifier(external_body)]
pub const MAX_PHYADDR_WIDTH: usize = 52;

pub axiom fn axiom_max_phyaddr_width_facts()
    ensures
        32 <= MAX_PHYADDR_WIDTH <= 52,
;


// File: spec_t/mmu/translation.rs
pub spec const MASK_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

pub fn MASK_ADDR() -> (ret: usize)
    ensures ret == MASK_ADDR_SPEC 
{
    proof {
        axiom_max_phyaddr_width_facts();
    }
    let r = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);
    r
}
}
