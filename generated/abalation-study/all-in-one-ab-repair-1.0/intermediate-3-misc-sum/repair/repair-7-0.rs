
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
        proof {
            // Adding the proof is important but the calculation must be + too in the assertion
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

}

### Changes Applied:
1. **Proof inside the loop:** The `proof` block inside the loop checks that `arith_sum_int(i as nat + 1) == arith_sum_int(i as nat) + (i as nat + 1)` ensures that the arithmetic sum calculated by adding a new integer is validated.
2. **Proof at the end:** Added a proof block at the end of the loop ensuring that `arith_sum_int(i as nat)` equals `arith_sum_int(n as nat)` before returning the final `sum`.

### Environment:
Ensure you are using the correct commands in the Verus verification environment to avoid generic "multiple input filenames" errors.

bash
verus hhhh.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmptmv9ke3p`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 11
// Safe: False