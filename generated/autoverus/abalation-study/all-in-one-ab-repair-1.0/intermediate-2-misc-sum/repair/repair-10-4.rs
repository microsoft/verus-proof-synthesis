
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
                if i != 0 {
                    assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i);
                    assert(arith_sum_int(i as nat) == arith_sum_int(i as int) as nat);
                }
            }
            i = i + 1;
            sum = sum + i;
        }
        assert(arith_sum_int(n as nat) == sum);
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8vlu5d7i`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True