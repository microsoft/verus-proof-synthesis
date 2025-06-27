
sum = sum + i; // This actually adds (i + 1)

Correcting this to:
rust
let old_i = i;
i = i + 1;
sum = sum + old_i; // Adds the previous value of 'i'
We also need to ensure that loop invariants are correctly formulated.

Fix the function like below:

rust
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
        while i < n
            invariant
                arith_sum_int(n as nat) < 10000,
                i <= n,
                sum == arith_sum_int(i as nat),
        {
            // Save the current value of i before updating it
            let old_i = i;
            // After updating i, we need to ensure arith_sum_int(i as nat)
            i = i + 1;
            // Update the sum using the old value of i
            sum = sum + old_i;
        }
        // Ensuring the loop invariant holds after the loop exits
        proof {
            assert(sum == arith_sum_int(n as nat));
        }
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpujshoq3n`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False