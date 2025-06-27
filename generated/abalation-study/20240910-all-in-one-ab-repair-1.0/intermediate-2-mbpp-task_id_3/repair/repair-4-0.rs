
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
        let mut index = 2;

        let ghost is_reorder; // Added by AI for postcondition

        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if (n % index) == 0 {
                proof{
                    is_reorder = true;  // Added by AI for postcondition
                }
                return true;
            }
            index += 1;
        }

        proof {
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            is_reorder = false;  // Added by AI for postcondition
        }

        false

        proof {
            assert(result == is_reorder); // Added by AI for postcondition
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpksrpa0qr`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False