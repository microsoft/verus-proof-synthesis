
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
    // Adding the proper proof for multiplication bounds
    // This proof uses the fact that the maximum value of x and y is 0xffff (65535)
    // Hence, the multiplication x * y will be at most 65535 * 65535 = 4294836225 < 0x100000000

    // Note: The max value of x and y is 2^16 - 1, thus:
    assert(0xffff * 0xffff == 4294836225);
    // Asserting that 4294836225 is less than 0x100000000 (4294967296)
    assert(4294836225 <= 0x100000000);

    // This implies, for any x, y <= 0xffff, the product will be less than or equal to 0x100000000
    assert(x * y <= 0xffff * 0xffff);
    assert(x * y <= 0x100000000);
}
}

// Score: (0, 1)
// Safe: True