use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

macro_rules! bit {
    ($v:expr) => {
        1usize << $v
    }
}

pub(crate) use bit;

// File: spec_t/mmu/translation.rs
pub const MASK_DIRTY_ACCESS: usize = bit!(5) | bit!(6);

pub const MASK_NEG_DIRTY_ACCESS: usize = !MASK_DIRTY_ACCESS;


// File: impl_u/l2_impl.rs
pub proof fn lemma_bitvector_facts()
    ensures
        forall|v: usize| v & bit!(5) == 0 && v & bit!(6) == 0 ==> #[trigger] (v & MASK_NEG_DIRTY_ACCESS) == v,
        forall|v: usize, i: usize| i < 64 ==> v & bit!(i) != bit!(i) <==> v & bit!(i) == 0,
        forall|v: usize| 0 & v == 0,
        forall|v: usize, m: usize| v & m & m == v & m,
        forall|v: usize| v & bit!(0) == #[trigger] (v & MASK_NEG_DIRTY_ACCESS & bit!(0)),
        forall|v: usize| v == v | 0,
{
}


}
