
use vstd::prelude::*;
fn main() {}

verus! {

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
            *old(sum) == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
    {
        if idx < n {
            let next_idx = idx + 1;
            *sum += next_idx;
            proof {
                // assert preconditions of the next recursive call
                assert(next_idx <= n);
                assert(*old(sum) == triangle(next_idx as nat - 1));
                assert(triangle(n as nat) < 0x1_0000_0000);
            }
            tail_triangle(n, next_idx, sum);
        }
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_3gkgf11`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False