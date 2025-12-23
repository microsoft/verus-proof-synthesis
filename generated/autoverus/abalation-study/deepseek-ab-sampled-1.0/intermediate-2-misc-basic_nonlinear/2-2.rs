
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
        // Establish the upper bound for x and y
        have h1: x <= 0xffff := by assumption;
        have h2: y <= 0xffff := by assumption;
        
        // Compute the maximum product
        let max_prod: u32 = 0xffff * 0xffff;
        
        // The product of x and y cannot exceed the maximum product
        have h3: x * y <= max_prod := by
            apply mul_le_mul_of_le_left;
            assumption; // x <= 0xffff
            assumption; // y <= 0xffff
        
        // Show that the maximum product is less than 0x100000000
        assert max_prod < 0x100000000;
        {
            norm_num; // Simplifies numerical expressions
        }
        
        // Combine the results to conclude the proof
        have h4: x * y < 0x100000000 := by
            nlinarith; // Solves inequalities involving numerical expressions
        }
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1