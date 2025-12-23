

use vstd::prelude::*;

fn main() {}

verus! {

    proof fn bound_check(x: u32, y: u32)
        requires
            x <= 0xffff,
            y <= 0xffff,
        ensures
            x * y <= 0x100000000,
    {
        assert(x <= 0xffff);
        assert(y <= 0xffff);
        // Compute the maximum possible product of x and y
        assert(x * y <= 0xffff * 0xffff);
        // Calculate 0xffff * 0xffff (which equals 0x100000000 - 1)
        assert(0xffff * 0xffff == 0x100000000 - 1);
        // Thus, x * y is less than or equal to 0x100000000 - 1
        // Which implies x * y <= 0x100000000
        assert(x * y <= 0x100000000);
    }
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2