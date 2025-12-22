use vstd::prelude::*;
use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}


verus! {

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

spec fn property_bounds_for_smallest_bitting_size(size:int) -> bool
{
    valid_bin_idx(smallest_bin_fitting_size(size)) &&
    size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bounds_for_smallest_bitting_size(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_bounds_for_smallest_bitting_size(size_start)
       && check_bounds_for_smallest_bitting_size(size_start + 1, size_end)
   }
}

proof fn result_bounds_for_smallest_bitting_size(size_start:int, size_end:int)
    ensures
        check_bounds_for_smallest_bitting_size(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_bounds_for_smallest_bitting_size(size)),
    decreases size_end - size_start,
{
   if size_start >= size_end {
   } else {
       result_bounds_for_smallest_bitting_size(size_start + 1, size_end);
   }
}

pub const BIN_HUGE: u64 = 73;

}
