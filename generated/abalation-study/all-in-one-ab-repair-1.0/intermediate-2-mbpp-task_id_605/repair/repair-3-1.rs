
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_divisible(n: int, divisor: int) -> bool {
        (n % divisor) == 0
    }

    fn prime_num(n: u64) -> (result: bool)
        requires
            n >= 2,
        ensures
            result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
    {
        if n <= 1 {
            unreachable!(); // should not reach here due to precondition
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if ((n % index) == 0) {
                return false;
            }
            index += 1;

            proof {
                // After incrementing index, we need to prove that the invariant still holds.
                // Specifically, we need to show `forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k)` holds.
                assert(forall|k: int| 2 <= k < (index - 1) ==> !is_divisible(n as int, k));
            }
        }
        true
    }
}

Explanation of Invariants and Proof Blocks:
1. **Invariants:**
    - `2 <= index <= n`: Ensures `index` stays within valid bounds during the loop.
    - `forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k)`: Maintains that `n` is not divisible by any number between 2 and `index - 1`.

2. **Proof Blocks:**
    - Added assert statement to verify loop invariant when `index` is incremented:
        rust
        assert(forall|k: int| 2 <= k < (index - 1) ==> !is_divisible(n as int, k));
        

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpv_g3oobv`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 13
// Safe: False