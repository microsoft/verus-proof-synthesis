
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
            i = i + 1;
            sum = sum + i;
            proof {
                // Verify that the updated sum matches the arithmetic sum specification
                assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i);
                // Assert sum expresses correctly according to the spec function, knowing the previous invariants.
                assert(sum == arith_sum_int(i as nat));
            }
        }
        sum
    }
}

### Explanation:

1. **Loop Invariants**:
   rust
   i <= n,
   sum == arith_sum_int(i as nat),
   arith_sum_int(n as nat) < 10000,
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4jigl1mf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False