
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
                assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i as nat);
            }
        }
        
        proof {
            assert(i == n); // Ensuring that i reaches n at the end of the loop
            assert(arith_sum_int(i as nat) == arith_sum_int(n as nat));
        }

        sum
    }

} // verus!

This code defines a function `compute_arith_sum` that calculates the arithmetic sum of numbers from 0 to `n - 1`. The invariants inside the `while` loop and the proofs handle the verification for the correctness.

To run this, ensure your verification tool is set correctly, and there are no extraneous input files or incorrect command-line arguments.

If you're running into specific tool-related issues (such as command-line invocation problems), please ensure you're following the correct steps to invoke `verus`. Here is a basic example of how you might compile and run it:

1. Ensure you have Verus installed and set up correctly.
2. Save your Rust code in a file, say `arith_sum.rs`.
3. Use the correct Verus command to verify your code, something similar to:
   verus arith_sum.rs
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpomsi4fid`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 13
// Safe: False