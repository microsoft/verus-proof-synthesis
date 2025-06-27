
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
            arith_sum_int(n as nat) < 10000,  // Adding a requirement to ensure the computed sum is less than 10000
        ensures
            arith_sum_int(n as nat) == sum,  // The computed sum is equal to the arithmetic sum of the first `n` numbers
    {
        let mut i: u64 = 0;
        let mut sum: u64 = 0;
        while i < n
            invariant
                arith_sum_int(n as nat) < 10000,
                i <= n,
                sum == arith_sum_int(i as nat),
        {
            i = i + 1;
            proof {
                assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i as nat); // Validate correctness of the summation logic
            }
            sum = sum + i;
            proof {
                assert(i <= n);
                assert(sum == arith_sum_int(i as nat));
            }
        }
        proof {
            assert(arith_sum_int(i as nat) == sum);
        }
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpc146q3jj`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False