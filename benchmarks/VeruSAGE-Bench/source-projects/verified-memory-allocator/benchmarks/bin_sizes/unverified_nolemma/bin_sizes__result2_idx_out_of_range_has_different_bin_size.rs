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

pub open spec fn pfd_lower(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if bin_idx == 1 {
        0
    } else {
        size_of_bin(bin_idx - 1) / INTPTR_SIZE as nat + 1
    }
}

pub open spec fn pfd_upper(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    size_of_bin(bin_idx) / INTPTR_SIZE as nat
}

spec fn property_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize:int) -> bool
{
    valid_bin_idx(bin_idx) &&
    !(pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx)) && 
    0 <= wsize <= 128 
    ==> 
    smallest_bin_fitting_size(wsize * INTPTR_SIZE) != bin_idx
}

spec fn check_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize_start:int, wsize_end:int) -> bool
    decreases wsize_end - wsize_start,
{
   if wsize_start >= wsize_end {
       true
   } else {
          property_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start)
       && check_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start + 1, wsize_end)
   }
}

spec fn check2_idx_out_of_range_has_different_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
    if bin_idx_start >= bin_idx_end {
        true
    } else {
        check_idx_out_of_range_has_different_bin_size(bin_idx_start, wsize_start, wsize_end)
        && check2_idx_out_of_range_has_different_bin_size(bin_idx_start + 1, bin_idx_end, wsize_start, wsize_end)
    }
}

proof fn result2_idx_out_of_range_has_different_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int)
    ensures
        check2_idx_out_of_range_has_different_bin_size(bin_idx_start, bin_idx_end, wsize_start, wsize_end) ==>
            (forall |bin_idx,wsize| bin_idx_start <= bin_idx < bin_idx_end && wsize_start <= wsize < wsize_end ==>
                     property_idx_out_of_range_has_different_bin_size(bin_idx, wsize)),
{

}


pub const INTPTR_SIZE: u64 = 8;

pub const BIN_HUGE: u64 = 73;

global size_of usize == 8;


}
