
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
        proof {
            assert(arith_sum_int(i as nat + 1) == arith_sum_int(i as nat) + (i as nat + 1));
        }

        i = i + 1;
        sum = sum + i;
    }
    
    proof {
        assert(arith_sum_int(i as nat) == arith_sum_int(n as nat)); // Validate final state
    }

    sum
}

} // verus!

Let’s break the verification specific part more clearly:

1. **Invariant Area**:
    - Ensure it holds `i <= n`.
    - Validate `sum` correctly represents `arith_sum_int(i as nat)`.
    - Check that the overall sum condition `arith_sum_int(n as nat) < 10000` is maintained.

2. **Proof Block Inside Loop**:
    - Ensure the sum invariant translates correctly: `assert(arith_sum_int(i as nat + 1) == arith_sum_int(i as nat) + (i as nat + 1));`.

3. **Final Proof Block**:
    - Assertion to verify `arith_sum_int(i as nat) == arith_sum_int(n as nat)` before returning sum.

If you are still experiencing input filename issues, ensure you are:

1. Using the correct filenames and file paths.
2. Properly invoking the compiler or verification tool without syntax or input errors.

For example, run your Rust/Verus code from the terminal as:

sh
verus compute_arith_sum.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4n0zyf6k`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 14
// Safe: False