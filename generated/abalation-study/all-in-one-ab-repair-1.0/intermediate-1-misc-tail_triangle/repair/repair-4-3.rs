
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
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
            triangle(n as nat) < 0x1_0000_0000,
            *sum == triangle(idx as nat), // Adjusted this line
        ensures
            *sum == triangle(n as nat),
    {
        let old_sum = *sum; // Capture the initial state of sum for proof
        if idx < n {
            let next_idx = idx + 1;
            *sum = *sum + next_idx;
            tail_triangle(n, next_idx, sum);
        }
        proof {
            assert(triangle(next_idx as nat) == *sum); // Ensures the recursive call maintains the invariant
        }
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgaopuumd`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False