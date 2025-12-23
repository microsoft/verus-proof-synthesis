
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
            result == (exists|k: int| 2 <= k < n as int && is_divisible(n as int, k)),
    {
        let ghost original_n = n as int;
        
        if n <= 1 {
            // This block will never be executed due to the precondition n >= 2.
            proof {
                assert(false); // Added for invariance
            }
            return true;
        }
        
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(original_n, k),
                n >= 2,
        {
            if is_divisible(original_n, index) {
                proof {
                    assert(exists|k: int| 2 <= k < n as int && is_divisible(original_n, k)); // Added
                }
                return true;
            }
            index += 1;
        }
        
        proof {
            assert(!exists|k: int| 2 <= k < n as int && is_divisible(original_n, k)); // Added
        }
        false
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa8dmri83`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False