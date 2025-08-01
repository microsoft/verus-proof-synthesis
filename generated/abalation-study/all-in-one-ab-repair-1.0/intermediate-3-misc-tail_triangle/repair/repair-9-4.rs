
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
            *sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
    {
        if idx < n {
            let idx_new = idx + 1;
            *sum += idx_new;
            proof {
                assert(*sum == triangle(idx as nat) + idx_new);
                assert(triangle(idx_new as nat) == triangle(idx as nat) + idx_new);
            }
            tail_triangle(n, idx_new, sum);
        } else {
            // Ensuring *sum == triangle(n as nat) when idx == n
            assert(*sum == triangle(n as nat));
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2ti32i_0`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False