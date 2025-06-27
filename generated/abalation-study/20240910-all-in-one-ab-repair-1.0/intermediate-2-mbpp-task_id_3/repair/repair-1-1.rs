
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_divisible(n: int, divisor: int) -> bool {
        (n % divisor) == 0
    }

    fn is_non_prime(n: u64) -> (result: bool)
        requires
            n >= 2,
        ensures
            result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
    {
        if n <= 1 {
            return true;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                index as u64 <= n,
                n >= 2,
        {
            if (n % index == 0) {
                return true;
            }
            index += 1;
        }
        false
    }
} // verus!

**Explanation of Changes:**

1. **Invariant Simplification:**
   We removed the redundant invariant:
   rust
   forall|j: int| 2 <= j < index ==> !is_divisible(n as int, j),
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpro8yu4p9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False