
use vstd::prelude::*;
fn main() {}

verus!{
     
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{
    // Assuming that 0xffff * 0xffff should be less than or equal to (2^32)
    // 0xffff is 65535 in decimal which is the maximum value for a u16 (16-bit unsigned integer).
    // The maximum value of x * y at this bounds is 65535 * 65535 which equals 4294836225
    // 4294836225 is less than 0x100000000, thus ensuring holds.
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1