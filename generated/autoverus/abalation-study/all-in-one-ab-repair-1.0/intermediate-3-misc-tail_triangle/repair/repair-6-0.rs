
use vstd::prelude::*;
fn main() {}

verus! {
    // Specification function to define the triangular number sequence
    #[verifier::loop_invariant(false)]
    spec fn triangle(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            n + triangle((n - 1) as nat)
        }
    }

    // Function to calculate triangular number using tail recursion
    fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *old(sum) == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
    {
        proof {
            // Add ghost variable to capture the current triangle value for idx
            let ghost old_triangle = triangle(idx as nat);
            // Assert initial state
            assert(*sum == old_triangle);
        }
        if idx < n {
            let idx1 = idx + 1;
            *sum = *sum + idx1;
            proof {
                // Update the ghost variable after addition
                let ghost new_triangle = triangle(idx1 as nat);
                // Check intermediate state
                assert(new_triangle == old_triangle + idx1 as nat);
                // Sum after recursion step is as expected
                assert(*sum == new_triangle);
            }
            tail_triangle(n, idx1, sum);
        }
        proof {
            // Add assertion for post state of the function
            assert(*sum == triangle(n as nat));
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_x4kwqpp`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False