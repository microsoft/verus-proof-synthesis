

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
        // We need to prove that if x and y are ≤ 0xffff, then x * y ≤ 0x100000000.
        assert!(x <= 0xffff);
        assert!(y <= 0xffff);

        // Compute the maximum value when x and y are both 0xffff.
        let max_x = 0xffff as u32;
        let max_y = 0xffff as u32;

        // The product of the maximum values.
        let product = max_x * max_y;

        // We know that (0xffff) * (0xffff) = 0xfffe0001, which is ≤ 0x100000000.
        assert!(product <= ( 0x100000000 ) as int);

        // Since x and y are each ≤ 0xffff, their product will also be ≤ 0xfffe0001, which is ≤ 0x100000000.
        assert!(x * y <= 0x100000000);
    }
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1