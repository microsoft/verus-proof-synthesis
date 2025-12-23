
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
            proof {
                assert(idx + 1 <= n);
                assert(*sum + (idx + 1) == triangle(idx as nat) + (idx + 1));
                assert(*sum + (idx + 1) < 0x1_0000_0000); // Ensure sum doesn't exceed the limit.
            }
            let idx = idx + 1;
            *sum = *sum + idx;
            tail_triangle(n, idx, sum);
        } else {
            proof {
                assert(*sum == triangle(n as nat));
            }
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9jagra9p`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False