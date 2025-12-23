
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
        let ghost original_n = n;
        let mut result = false;

        if n <= 1 {
            // This block will never be executed due to the precondition n >= 2.
            result = true;
        } else {
            let mut index = 2;
            while index < n
                invariant
                    2 <= index <= n,
                    forall|k: int| 2 <= k < index ==> !is_divisible(original_n as int, k),
                    n >= 2,
            {
                if (n % index) == 0 {
                    result = true;
                    break;
                }
                index += 1;
            }
        }
        
        proof {
            if result {
                assert(exists|k: int| 2 <= k < n && is_divisible(original_n as int, k)) by {
                    assert(n >= 2);
                    if n > 1 {
                        assert(result);
                        assert(exists |k: int| 2 <= k < n && is_divisible(n as int, k));
                    }
                }
            } else {
                assert(!exists|k: int| 2 <= k < n && is_divisible(original_n as int, k)) by {
                    assert(n >= 2);
                    if n > 1 {
                        assert(!result);
                        forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k);
                    }
                }
            }
        }

        result
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphlywrp36`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False