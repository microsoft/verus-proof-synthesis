
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
        // We know that x and y are each at most 0xffff.
        // Therefore, their product is at most 0xffff * 0xffff = 0xfffe0001,
        // which is less than 0x100000000.
        assert!(x <= 0xffff);
        assert!(y <= 0xffff);
        assert!(x * y <= 0xffff * 0xffff);
        assert!(0xffff * 0xffff <= 0x100000000);
        assert!(x * y <= 0x100000000);
    }
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1