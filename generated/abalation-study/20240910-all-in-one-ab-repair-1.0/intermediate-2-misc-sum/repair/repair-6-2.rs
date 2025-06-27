
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
            sum = sum + (i + 1);
            i = i + 1;
            proof {
                assert(i <= n);
                assert(arith_sum_int(n as nat) < 10000);
                assert(sum == arith_sum_int(i as nat));
            }
        }
        assert(arith_sum_int(n as nat) == sum);
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpc0u6xmyx`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False