
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
            proof {
                assert(i as int >= 0); // Ensure i is non-negative at the start
                if i > 0 {
                    assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i as nat);
                    assert(sum + i + 1 == arith_sum_int((i + 1) as nat));
                }
            }
            sum = sum + (i + 1); // Correct sum update
            i = i + 1;
        }
        proof {
            assert(arith_sum_int(i as nat) == sum);
        }
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpeh2nwpes`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False