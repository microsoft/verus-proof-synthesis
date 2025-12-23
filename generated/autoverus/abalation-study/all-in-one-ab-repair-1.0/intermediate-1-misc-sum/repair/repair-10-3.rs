
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn arith_sum_int(i: nat) -> nat
        decreases i,
    {
        if i == 0 {
            0
        } else {
            i + arith_sum_int((i - 1) as nat)
        }
    }

    fn compute_arith_sum(n: u64) -> (sum: u64)
        requires
            arith_sum_int(n as nat) < 10000,
        ensures
            arith_sum_int(n as nat) == sum,
    {
        let mut i: u64 = 0;
        let mut sum: u64 = 0;
        while i <= n  // Correcting the loop condition to include `n`
            invariant
                arith_sum_int(n as nat) < 10000,
                i <= n,
                sum == arith_sum_int(i as nat - 1) if i > 0 else 0,
        {
            sum = sum + i; // Use `i` before increment
            i = i + 1;
        }
        // Ensuring the loop invariant holds after the loop exits
        // sum == arith_sum_int(n as nat) is already ensured by the invariant

        // Fix invariant violation for final condition
        sum = sum + i; // Perform the final addition for `i == n`
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpfp9uyox_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False