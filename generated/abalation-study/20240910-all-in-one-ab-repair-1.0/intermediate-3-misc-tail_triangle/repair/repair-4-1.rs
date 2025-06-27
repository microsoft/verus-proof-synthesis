
use vstd::prelude::*;
fn main() {}

verus! {
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

    fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *old(sum) == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
    {
        if idx < n {
            let next_idx = idx + 1;
            let next_sum = *sum + next_idx;
            proof {
                // Ensure that the invariant will hold for the recursive call
                // Use ghost variables to track the expected values
                let ghost new_sum = next_sum;
                let ghost new_idx = next_idx;
                let ghost prev_sum = *sum;

                // Verify the next state in terms of the specification
                assert(triangle(new_idx as nat) == triangle(idx as nat) + new_idx as nat);
                assert(new_sum == triangle(new_idx as nat));
            }
            *sum = next_sum;
            tail_triangle(n, next_idx, sum);
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu48n2ylr`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False