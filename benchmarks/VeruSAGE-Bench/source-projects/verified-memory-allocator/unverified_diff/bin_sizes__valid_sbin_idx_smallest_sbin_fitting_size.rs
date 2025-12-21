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

pub const SEGMENT_BIN_MAX: usize = 31;

pub const SLICE_SIZE: u64 = 65536;

pub const INTPTR_SHIFT: u64 = 3;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub open spec fn valid_sbin_idx(sbin_idx: int) -> bool {
    0 <= sbin_idx <= SEGMENT_BIN_MAX
}

pub open spec fn smallest_sbin_fitting_size(i: int) -> int
{
    if i <= 8 {
        i
    } else {
        let w = (i - 1) as u64;
        //let lz = w.leading_zeros();
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let sbin_idx = ((b << 2u8) as u64 | ((w >> (b as u64 - 2) as u64) & 0x03)) - 4;
        sbin_idx
    }
}

spec fn property_sbin_idx_smallest_sbin_fitting_size(size:int) -> bool
{
    valid_sbin_idx(smallest_sbin_fitting_size(size))
}

spec fn check_sbin_idx_smallest_sbin_fitting_size(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin_idx_smallest_sbin_fitting_size(size_start)
       && check_sbin_idx_smallest_sbin_fitting_size(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_sbin_idx_smallest_sbin_fitting_size(size_start:int, size_end:int)
    ensures
        check_sbin_idx_smallest_sbin_fitting_size(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin_idx_smallest_sbin_fitting_size(size)),
    decreases size_end - size_start,
{
   unimplemented!()
}

pub proof fn valid_sbin_idx_smallest_sbin_fitting_size(i: int)
    requires 0 <= i <= SLICES_PER_SEGMENT
    ensures valid_sbin_idx(smallest_sbin_fitting_size(i)),
{
}

}
