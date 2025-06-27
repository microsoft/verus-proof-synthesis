
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
            proof {
                // Proving the invariant holds after 'sum' is updated
                // Note: After incrementing 'i', it reflects in the sum calculation
                assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i as nat);
            }
        }
        
        proof {
            // Final proof to verify the postcondition
            // Ensuring that 'i' reaches 'n' at the end and thereby sum is correctly computed
            assert(i == n);
            assert(arith_sum_int(i as nat) == arith_sum_int(n as nat));
        }

        sum
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp720oh21d`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: True