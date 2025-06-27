
use vstd::prelude::*;
fn main() {}

// Verus block to verify the code.
verus! {
    // Function to calculate the triangular number non-tail recursively.
    spec fn triangle(n: nat) -> nat
        decreases n, // Specifies that n must decrease with each recursive call (ensuring termination)
    {
        // Base case: n == 0. The triangular number of 0 is 0.
        if n == 0 {
            0
        } else {
            // Recursive case: the triangular number of n is n plus the triangular number of n - 1.
            n + triangle((n - 1) as nat)
        }
    }

    // Tail recursive function to calculate the triangular number.
    fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n, // Ensures that the starting index is less than or equal to n.
            *old(sum) == triangle(idx as nat), // Ensures the sum is correct up to the current index.
            triangle(n as nat) < 0x1_0000_0000, // Ensures the result fits within a 32-bit integer.
        ensures
            *sum == triangle(n as nat), // Ensures that the final sum is the triangular number of n.
    {
        // Base case: If idx is equal to n, do nothing (recursive calls stop here).
        if idx < n {
            // Increment the index.
            let idx = idx + 1;
            // Add the new index value to the sum.
            *sum = *sum + idx;
            // Recursively call the function with the updated index and sum.
            tail_triangle(n, idx, sum);
        }
    }
}


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2