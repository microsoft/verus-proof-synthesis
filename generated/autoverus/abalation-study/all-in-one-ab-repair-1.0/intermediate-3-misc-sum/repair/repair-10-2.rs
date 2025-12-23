
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
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
            sum = sum + (i + 1); // Adjusted to ensure sum reflects the correct arithmetic sum state
            i = i + 1;
            proof {
                // The sum invariant must still hold
                assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i as nat);
            }
        }

        proof {
            // Ensuring completion of the loop
            assert(i == n); 
            assert(arith_sum_int(i as nat) == arith_sum_int(n as nat));
        }

        sum
    }
} // verus!



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpb5q5xi0j`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False