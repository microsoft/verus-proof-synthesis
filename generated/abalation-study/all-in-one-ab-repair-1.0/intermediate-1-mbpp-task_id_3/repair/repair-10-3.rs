
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

        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                n >= 2,
                forall|k: int| 2 <= k < index ==> !is_divisible(original_n as int, k),
        {
            if (n % index) == 0 {
                proof {
                    assert(exists|k: int| 2 <= k < n && is_divisible(original_n as int, k));
                }
                return true;
            }
            index += 1;
        }

        proof {
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(original_n as int, k));
            assert(!exists|k: int| 2 <= k < n && is_divisible(original_n as int, k));
        }

        false
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpfe95s3et`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 3
// Safe: False