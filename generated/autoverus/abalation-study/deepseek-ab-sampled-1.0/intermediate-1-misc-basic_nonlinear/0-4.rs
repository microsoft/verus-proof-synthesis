

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
    assert(x*y <= x*0xffff);
    assert(x*y <= 0xffff*0xffff);
    assert(0xffff * 0xffff <= 0x100000000);
    // To understand this step, note that 0xffff is 2^16 - 1. Therefore, 0xffff * 0xffff = (2^16 - 1)^2 = 2^32 - 2^17 + 1, which is less than 2^32 (0x100000000).
 }
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1