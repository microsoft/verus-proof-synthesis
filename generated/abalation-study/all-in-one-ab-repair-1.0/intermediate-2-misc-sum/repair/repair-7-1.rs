
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
            i + arith_sum_int(i - 1) // Fixed type cast issue
        }
    }

    fn compute_arith_sum(n: u64) -> (sum: u64)
        requires
            arith_sum_int(n as nat) < 10000,
        ensures
            arith_sum_int(n as nat) == sum,
    {
        if n == 0 {
            return 0; // Base case for n == 0
        }
        let mut i: u64 = 0;
        let mut sum: u64 = 0;
        while i < n
            invariant
                i <= n,
                sum == arith_sum_int(i as nat),
                arith_sum_int(n as nat) < 10000, // Ensure valid sum calculation
        {
            i = i + 1;
            sum = sum + i;
            assert(arith_sum_int(i as nat) == sum);
        }
       
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp6q82cnon`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False