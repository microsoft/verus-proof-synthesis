use vstd::prelude::*;
use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}

verus! {

spec fn property_sbin_bounds(size:int) -> bool
{
    let lz = u64_leading_zeros(size as u64);
    let b = (63 - lz) as u8;
    // Satisfy various type requirements
    (b  >= 2) &&
    (((b << 2u8) as u64 | ((size as u64 >> (b as u64 - 2) as u64) & 0x03)) >= 4) 
}

spec fn check_sbin_bounds(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin_bounds(size_start)
       && check_sbin_bounds(size_start + 1, size_end)
   }
}

proof fn result_sbin_bounds(size_start:int, size_end:int)
    ensures
        check_sbin_bounds(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin_bounds(size)),
    decreases size_end - size_start,
{
   if size_start >= size_end {
   } else {
       result_sbin_bounds(size_start + 1, size_end);
   }
}

}
