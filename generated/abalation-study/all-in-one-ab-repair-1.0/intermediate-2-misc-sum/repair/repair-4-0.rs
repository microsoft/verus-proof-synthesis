

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
            i += 1;
            sum += i;
            proof {
                // Update the invariant to ensure sum is correctly maintaining the relation with arith_sum_int
                assert(i <= n);
                assert(sum == arith_sum_int(i as nat));
                assert(arith_sum_int(n as nat) < 10000);
            }
        }
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkb2dzdmf`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False