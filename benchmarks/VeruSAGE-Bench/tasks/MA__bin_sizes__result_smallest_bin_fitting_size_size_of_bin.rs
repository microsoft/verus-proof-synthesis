use vstd::prelude::*;

use vstd::std_specs::bits::u64_leading_zeros;
fn main() {}


verus! {

/*
Definitions from vstd
-----
vstd::std_specs::bits
-----
#[verifier::opaque]
pub open spec fn u64_leading_zeros(i: u64) -> int
    decreases i,
{
    if i == 0 {
        64
    } else {
        u64_leading_zeros(i / 2) - 1
    }
}
-----
*/

pub const BIN_HUGE: u64 = 73;

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

pub open spec fn smallest_bin_fitting_size(size: int) -> int {
    let bytes_per_word = (usize::BITS / 8) as int;
    let wsize = (size + bytes_per_word - 1) / bytes_per_word;
    if wsize <= 1 {
        1
    } else if wsize <= 8 {
        wsize
    } else if wsize > 524288 {
        BIN_HUGE as int
    } else {
        let w = (wsize - 1) as u64;
        //let lz = w.leading_zeros();
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let shifted = (w >> (b - 2) as u64) as u8;
        let bin_idx = ((b * 4) + (shifted & 0x03)) - 3;
        bin_idx
    }
}

spec fn property_smallest_bin_fitting_size_size_of_bin(bin_idx:int) -> bool
{
    smallest_bin_fitting_size(size_of_bin(bin_idx) as int) == bin_idx
}

spec fn check_smallest_bin_fitting_size_size_of_bin(bin_idx_start:int, bin_idx_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
   if bin_idx_start >= bin_idx_end {
       true
   } else {
          property_smallest_bin_fitting_size_size_of_bin(bin_idx_start)
       && check_smallest_bin_fitting_size_size_of_bin(bin_idx_start + 1, bin_idx_end)
   }
}

proof fn result_smallest_bin_fitting_size_size_of_bin(bin_idx_start:int, bin_idx_end:int)
    ensures
        check_smallest_bin_fitting_size_size_of_bin(bin_idx_start, bin_idx_end) ==>
            (forall |bin_idx| bin_idx_start <= bin_idx < bin_idx_end ==>
                 property_smallest_bin_fitting_size_size_of_bin(bin_idx)),
{

}

}
