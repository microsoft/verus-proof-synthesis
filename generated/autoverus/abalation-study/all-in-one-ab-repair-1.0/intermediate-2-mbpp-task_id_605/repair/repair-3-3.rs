
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
            return false;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2, // This invariant is already enforced by loop condition
        {
            if (n % index) == 0 {
                return false;
            }
            index += 1;
            proof {
                // Here, we show that the invariant still holds after incrementing index
                // Specifically, we need to show `forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k)` holds.
                assert(index <= n); // This asserts the index is still within bounds
            }
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpk0o7r6k6`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False