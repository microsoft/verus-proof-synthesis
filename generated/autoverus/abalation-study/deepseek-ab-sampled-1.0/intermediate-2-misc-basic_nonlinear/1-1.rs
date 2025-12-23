

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
    assert(
        x <= 0xffff,
        "Given constraint x <= 0xffff is satisfied",
    );
    assert(
        y <= 0xffff,
        "Given constraint y <= 0xffff is satisfied",
    );
    assert(
        (x * y) <= (0x10000u32) * (0x10000u32),
        "Multiplying the maximum 16-bit values gives a 32-bit result",
    );
    assert(
        (x * y) <= 0x100000000,
        "The product of two 16-bit values does not exceed 2^32",
    );
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1