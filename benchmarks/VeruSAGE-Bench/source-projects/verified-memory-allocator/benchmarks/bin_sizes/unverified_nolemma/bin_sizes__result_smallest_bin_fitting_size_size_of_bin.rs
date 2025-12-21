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

pub const BIN_HUGE: u64 = 73;

}
