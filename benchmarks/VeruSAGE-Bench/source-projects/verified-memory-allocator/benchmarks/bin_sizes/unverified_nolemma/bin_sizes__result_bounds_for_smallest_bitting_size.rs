use vstd::prelude::*;
use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}


verus! {

pub open spec fn valid_bin_idx(bin_idx: int) -> bool {
    1 <= bin_idx <= BIN_HUGE
}

	#[verifier::external_body]
pub open spec fn size_of_bin(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
	{
		unimplemented!()
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
{
}

pub const BIN_HUGE: u64 = 73;

}
