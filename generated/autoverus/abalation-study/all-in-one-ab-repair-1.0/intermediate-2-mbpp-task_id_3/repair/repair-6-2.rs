
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
        if n <= 2 {
            proof {
                assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k) == false);
            }
            return false; // n = 2 is prime
        }
        
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if (n % index) == 0 {
                proof {
                    assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
                }
                return true;
            }
            index += 1;
        }
        
        proof {
            // Prove that no value in the range [2, index) divides n
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
        }
        
        false
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpuk7trked`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: False