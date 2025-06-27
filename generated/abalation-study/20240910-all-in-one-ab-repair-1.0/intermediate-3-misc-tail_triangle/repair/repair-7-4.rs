
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
        if idx < n {
            let new_idx = idx + 1;
            proof {
                let old_sum = *sum;
                *sum = *sum + new_idx;
                assert(old_sum == triangle(idx as nat));
                assert(*sum == old_sum + new_idx);
                assert(*sum == triangle(new_idx as nat));
            }
            tail_triangle(n, new_idx, sum);
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8lsf3kns`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False