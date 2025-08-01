
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
            i = i + 1;
            sum = sum + i;
            proof {
                assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i);
            }
        }
        assert(arith_sum_int(n as nat) == sum);
        sum
    }
}

### Explanation of changes and proof:
1. **Function Definitions and Invariant Adjustments**: 
    - The `arith_sum_int` function and the `compute_arith_sum` function are retained as in the original code.
    - The `arith_sum_int` function specification ensures that the input `i` is reduced in each recursive call with `decreases i`.

2. **Loop Invariant Proof**:
    - Within the while loop, the documentation to prove the correctness of the invariants:
      rust
      invariant
          i <= n,
          sum == arith_sum_int(i as nat),
          arith_sum_int(n as nat) < 10000,
    - Ensure loop invariants cover the relationship between `i`, `n`, and `sum`.
        
3. **Loop Body**:
    - Proving the arithmetic relationship incrementally in the loop body using:
      rust
      proof {
          assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i);
      }

4. **Final Assertion**:
    - At the end of the loop, confirm that the final `sum` is indeed the arithmetic sum up to `n`:
      rust
      assert(arith_sum_int(n as nat) == sum);
      

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2k2brw4x`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 21
// Safe: False