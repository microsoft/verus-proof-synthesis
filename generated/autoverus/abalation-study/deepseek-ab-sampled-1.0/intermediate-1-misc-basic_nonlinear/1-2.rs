
use vstd::prelude::*;
fn main() {}

verus! {
    proof fn bound_check(x: u32, y: u32)
        requires
            x <= 0xffff,
            y <= 0xffff,
        ensures
            x*y <= 0x100000000,
    {
        // We know that x and y are each at most 0xffff.
        have h1: u32 = 0xffff;
        have h2: x <= h1 by vertigo;
        have h3: y <= h1 by vertigo;

        // The maximum possible product is 0xffff * 0xffff, which is less than 0x100000000.
        assert(x * y <= h1 * h1);
        assert(h1 * h1 < 0x100000000 by vertigo);
        ergo;
    }
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1