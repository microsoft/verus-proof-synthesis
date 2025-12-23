
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
                forall|k: int| 2 <= k < index ==> !is_divisible(original_n as int, k),
                n >= 2,
        {
            if ((n % index) == 0) {
                proof {
                    assert(index < n);
                    assert(2 <= index < n);
                    assert(is_divisible(original_n as int, index));
                    assert(exists|k: int| 2 <= k < n && is_divisible(original_n as int, k));
                }
                return true;
            }
            index += 1;

            proof {
                assert(forall|k: int| 2 <= k < index ==> !is_divisible(original_n as int, k));
            }
        }

        proof {
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(original_n as int, k));
            // By the end of the loop, the forall assertion should imply that no such k exists, thus n is prime
            assert(!exists|k: int| 2 <= k < n && is_divisible(original_n as int, k));
        }

        false
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmps49_bj6h`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False