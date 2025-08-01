
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
        while i <= n
            invariant
                i <= n,
                sum == arith_sum_int(i as nat),
                arith_sum_int(n as nat) < 10000,
        {
            proof {
                // After we increase i, we need to check the condition again.
                assert(arith_sum_int(i as nat) < 10000);
            }
            
            sum = sum + i;
            i = i + 1;
            
            proof {
                // Verify the relations after the updates
                // In loop invariant checking, `proof` block assertion checks can be omitted.
                assert(arith_sum_int(n as nat) < 10000);
                assert(sum == arith_sum_int(i as nat));
            }
        }
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpomlwn5rl`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 4
// Safe: False