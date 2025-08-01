
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
                i <= n,
                sum == arith_sum_int(i as nat),
                arith_sum_int(n as nat) < 10000,
        {
            i = i + 1;
            sum = sum + i;

            // Proof block to maintain the invariant
            proof {
                assert(sum == arith_sum_int(i as nat + 1)); // Updated invariant assertion
            }
        }
        sum
    }
}

Ensure you are running the Verus tool correctly by specifying the correct input file. For example:
sh
verus_tool your_file.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpxhh6zv39`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False