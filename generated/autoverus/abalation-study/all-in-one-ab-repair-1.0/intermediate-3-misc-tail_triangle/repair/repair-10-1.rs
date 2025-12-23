
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

    fn tail_triangle(mut n: u32, mut idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
    {
        while idx < n
            invariant
                idx <= n,
                *sum == triangle(idx as nat),
                triangle(n as nat) < 0x1_0000_0000,
        {
            idx += 1;
            *sum += idx;
            // Ensure that the invariant is preserved
            proof {
                assert(*sum == triangle(idx as nat));
            }
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpjgx76ic3`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False