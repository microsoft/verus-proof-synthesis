
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
    // Using the fact that 0xffff is the maximum value for 16-bit unsigned integers
    // and 0x100000000 is 2^32, which is the range of 32-bit unsigned integer
    assert(x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64);
    assert(x as u64 * y as u64 <= 0xffffffff as u64); // 0xffff * 0xffff is less than 2^32
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1