
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
            // This branch is incorrect as per the requires clause
            // We shouldn't hit this branch since n >= 2
            proof {
                assert(false); // To make sure this branch is never taken
            }
            return true;
        }
        
        let mut index = 2;
        let mut found_divisor = false;

        while index < n && !found_divisor
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if (n % index) == 0 {
                found_divisor = true;
            }
            index += 1;
        }

        found_divisor

        proof {
            if found_divisor {
                assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
            } else {
                assert(!exists|k: int| 2 <= k < n && is_divisible(n as int, k));
            }
        }
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpyo2cyfkz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False