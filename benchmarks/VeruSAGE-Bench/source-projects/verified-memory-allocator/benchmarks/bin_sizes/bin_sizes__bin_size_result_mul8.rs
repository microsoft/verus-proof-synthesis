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

spec fn property_bin(size:int) -> bool
{
    131072 >= size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bin(size_start:int, size_end:int) -> bool
    decreases size_end - size_start + 8,
{
   if size_start >= size_end {
       true
   } else {
          property_bin(size_start)
       && check_bin(size_start + 8, size_end)
   }
}

spec fn id(i:int) -> bool { true }

	#[verifier::external_body]
proof fn result_bin(size_start:int, size_end:int)
    requires size_start % 8 == 0,
    ensures
        check_bin(size_start, size_end) ==>
            (forall |size: int| size_start <= size < size_end && size % 8 == 0 ==>
                 #[trigger] id(size) && property_bin(size)),
    decreases size_end - size_start + 8,
	{
		unimplemented!()
	}

pub proof fn bin_size_result_mul8(size: usize)
    requires
        size % 8 == 0,
        size <= 131072, //  == MEDIUM_OBJ_SIZE_MAX
        valid_bin_idx(smallest_bin_fitting_size(size as int)),
    ensures
        131072 >= size_of_bin(smallest_bin_fitting_size(size as int) as int) >= size,
{
    // TODO: Swap these asserts for the assumes below
    
        /*
	assert(check_bin(0, 8192)) by (compute_only);
	assert(check_bin(8192, 16384)) by (compute_only);
	assert(check_bin(16384, 24576)) by (compute_only);
	assert(check_bin(24576, 32768)) by (compute_only);
	assert(check_bin(32768, 40960)) by (compute_only);
	assert(check_bin(40960, 49152)) by (compute_only);
	assert(check_bin(49152, 57344)) by (compute_only);
	assert(check_bin(57344, 65536)) by (compute_only);
	assert(check_bin(65536, 73728)) by (compute_only);
	assert(check_bin(73728, 81920)) by (compute_only);
	assert(check_bin(81920, 90112)) by (compute_only);
	assert(check_bin(90112, 98304)) by (compute_only);
	assert(check_bin(98304, 106496)) by (compute_only);
	assert(check_bin(106496, 114688)) by (compute_only);
	assert(check_bin(114688, 122880)) by (compute_only);
	assert(check_bin(122880, 131080)) by (compute_only);
        */

	assume(check_bin(0, 8192));
	assume(check_bin(8192, 16384));
	assume(check_bin(16384, 24576));
	assume(check_bin(24576, 32768));
	assume(check_bin(32768, 40960));
	assume(check_bin(40960, 49152));
	assume(check_bin(49152, 57344));
	assume(check_bin(57344, 65536));
	assume(check_bin(65536, 73728));
	assume(check_bin(73728, 81920));
	assume(check_bin(81920, 90112));
	assume(check_bin(90112, 98304));
	assume(check_bin(98304, 106496));
	assume(check_bin(106496, 114688));
	assume(check_bin(114688, 122880));
	assume(check_bin(122880, 131080));

	result_bin(0, 8192);
	result_bin(8192, 16384);
	result_bin(16384, 24576);
	result_bin(24576, 32768);
	result_bin(32768, 40960);
	result_bin(40960, 49152);
	result_bin(49152, 57344);
	result_bin(57344, 65536);
	result_bin(65536, 73728);
	result_bin(73728, 81920);
	result_bin(81920, 90112);
	result_bin(90112, 98304);
	result_bin(98304, 106496);
	result_bin(106496, 114688);
	result_bin(114688, 122880);
	result_bin(122880, 131080);

    assert(id(size as int));
}


pub const BIN_HUGE: u64 = 73;

}
