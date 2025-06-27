
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
                2 <= n,
        {
            if ((n % index) == 0) {
                proof {
                    assert(is_divisible(n as int, index as int));
                    assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
                }
                return true;
            }
            index += 1;
        }
        
        proof {
            // Prove that no value in the range [2, n) divides n
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            assert(!exists|k: int| 2 <= k < n && is_divisible(n as int, k));
        }
        
        false
    }
} 

// Score: (2, 0)
// Safe: True