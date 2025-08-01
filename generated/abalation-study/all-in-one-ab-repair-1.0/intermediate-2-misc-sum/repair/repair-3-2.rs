
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
                // Assert the correctness of the sum after increment
                assert(arith_sum_int(i as nat) == sum);
            }
        }
        sum
    }

} // verus!

### Explanation of Changes:
1. **Invariant and Requires/Ensures**: Ensure that the loop invariant continues to uphold the expected behavior of the system.
2. **Simplified Proof Assertions**: The assertion of correctness within the loop implies that `arith_sum_int(i as nat) == sum`. Simply ensuring this after the increment should be sufficient based on the loop invariant.

### Recommendations:
- **Command Line Error**: Ensure there are no multiple filenames provided if running the `verus` command manually.
- **Verus Tool Invocation**: Make sure the command syntax matches Verus's expected input format. Normally, you might simply run the command as:
    sh
    verus hhhh.rs
    

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp964r2llh`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False