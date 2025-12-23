
use vstd::prelude::*;
fn main() {}

verus! {
    lemma mul_le_mul_left(a: u32, b: u32) requires a ≤ b ensures a * 1 ≤ b * 1;
    
    proof fn bound_check(x: u32, y: u32)
        requires
            x <= 0xffff,
            y <= 0xffff,
        ensures
            x*y <= 0x100000000,
    {
        // Apply the lemma to show that x * y ≤ 0x100000000
        mul_le_mul_left(x, 0xffff);
        mul_le_mul_left(y, 0xffff);
    }
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3