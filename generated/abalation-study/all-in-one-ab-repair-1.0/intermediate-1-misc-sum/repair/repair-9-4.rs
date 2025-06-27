
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
            // Update sum first to meet invariant in the next iteration
            sum = sum + i + 1;
            // After updating i, we need to ensure arith_sum_int(i as nat)
            i = i + 1;
        }
        assert(sum == arith_sum_int(n as nat));
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpjodbxsx5`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3
// Safe: False