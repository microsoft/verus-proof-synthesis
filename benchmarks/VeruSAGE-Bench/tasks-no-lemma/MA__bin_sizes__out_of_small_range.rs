use vstd::prelude::*;


fn main() {}

verus! {

global size_of usize == 8;

pub const INTPTR_SIZE: u64 = 8;

pub const BIN_HUGE: u64 = 73;

pub const SMALL_WSIZE_MAX: usize = 128;

pub const PAGES_DIRECT: usize = SMALL_WSIZE_MAX + 1;

pub const SMALL_SIZE_MAX: usize = SMALL_WSIZE_MAX * INTPTR_SIZE as usize;

pub open spec fn valid_bin_idx(bin_idx: int) -> bool {
    1 <= bin_idx <= BIN_HUGE
}

pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

#[verifier::opaque]
pub open spec fn size_of_bin(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if 1 <= bin_idx <= 8 {
       (usize::BITS / 8) as nat * (bin_idx as nat)
    } else if bin_idx == BIN_HUGE {
        // the "real" upper bound on this bucket is infinite
        // the lemmas on bin sizes assume each bin has a lower bound and upper bound
        // so we pretend this is the upper bound

        8 * (524288 + 1)
        //8 * (MEDIUM_OBJ_WSIZE_MAX as nat + 1)
    } else {
        let group = (bin_idx - 9) / 4;
        let inner = (bin_idx - 9) % 4;

        ((usize::BITS / 8) * (inner + 5) * pow2(group + 1)) as nat
    }
}

pub open spec fn pfd_lower(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if bin_idx == 1 {
        0
    } else {
        size_of_bin(bin_idx - 1) / INTPTR_SIZE as nat + 1
    }
}

pub proof fn out_of_small_range(bin_idx: int)
    requires valid_bin_idx(bin_idx),
        size_of_bin(bin_idx) > SMALL_SIZE_MAX,
    ensures
        pfd_lower(bin_idx) >= PAGES_DIRECT,
{
}
}
