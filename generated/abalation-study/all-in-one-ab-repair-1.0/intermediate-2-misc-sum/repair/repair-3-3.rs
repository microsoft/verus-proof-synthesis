
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::recursive_invariant]
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
        proof {
            // Initial invariant-state proof.
            assert(i <= n);
            assert(sum == arith_sum_int(i as nat));
        }
        while i < n
            invariant
                i <= n,
                sum == arith_sum_int(i as nat),
                arith_sum_int(n as nat) < 10000,
        {
            i = i + 1;
            sum = sum + i;
            proof {
                // Use helper-function proof within the loop.
                assert(new_sum: arith_sum_int(i) == sum);
            }
        }
        sum
    }

    // Helper function to assert the loop-invariant.
    proof fn sum_correctness_proof(new_i: u64, new_sum: u64)
        requires
            new_i > 0,
            // Add prerequisite-correction within such helper construct.
        ensures
            arith_sum_int(new_i as nat) == new_sum
    {
        assert(arith_sum_int(new_i as nat) == new_sum);
    }
}

Note: It is best to run Verus-specific tools reflectively, following file-specific verification-hints aligns post-hoc checking/inlining squared away via loop invariant and function-reordering.

Try running verification tools specific to Verus-Rust:
sh
verus my_file.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_0o6nuwr`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False