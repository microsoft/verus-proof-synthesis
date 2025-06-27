
use vstd::prelude::*;
fn main() {}

verus! {
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
        // Proof block to ensure the preconditions and postconditions are properly validated
        proof {
            assert(idx as nat <= n as nat);
        }

        if idx < n {
            *sum = *sum + (idx + 1);
            tail_triangle(n, idx + 1, sum);
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmcud0e8t`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2
// Safe: False