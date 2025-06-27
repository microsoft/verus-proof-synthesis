
use vstd::prelude::*;
fn main() {}

verus! {

    // Specification of the mathematical function for the triangle number sequence
    spec fn triangle(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            n + triangle(n - 1)
        }
    }

    fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *sum == triangle(idx as nat),  // Ensure `sum` starts with the correct triangle value for `idx`
            triangle(n as nat) < 0x1_0000_0000,  // Ensure `triangle(n)` fits within a u32
        ensures
            *sum == triangle(n as nat),  // Ensure `sum` ends up with the correct triangle value for `n`
    {
        if idx < n {
            let next_idx = idx + 1;
            *sum = *sum + next_idx;
            tail_triangle(n, next_idx, sum);  // Recursive call
        }
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpyij1x2qx`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False