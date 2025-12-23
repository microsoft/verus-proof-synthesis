
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
        proof {
            assert(triangle(n as nat) < 0x1_0000_0000);
        }

        if idx < n {
            let next_idx = idx + 1;
            *sum = *sum + next_idx;

            proof {
                assert(*sum == triangle(next_idx as nat)); // Added proof to ensure sum is correct
                assert(idx + 1 <= n); // Added proof
            }

            tail_triangle(n, next_idx, sum);
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpei_srhf_`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2
// Safe: False