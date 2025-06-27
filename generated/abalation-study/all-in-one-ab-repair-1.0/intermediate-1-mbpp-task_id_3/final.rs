
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

        if n <= 1 {
            // This block will never be executed due to the precondition n >= 2.
            return true;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                n >= 2,
                forall|k: int| 2 <= k < index ==> !is_divisible(original_n as int, k),
        {
            if ((n % index) == 0) {
                proof {
                    // Post the fact when finding a divisible number.
                    assert(exists|k: int| 2 <= k < n && is_divisible(original_n as int, k));
                }
                return true;
            }
            index += 1;
        }

        proof {
            // At this point, we've ruled out all possible divisors in the specified range.
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(original_n as int, k));
            // By the end of the loop, the forall assertion should imply that no such k exists, thus n is prime
            assert(!exists|k: int| 2 <= k < n && is_divisible(original_n as int, k));
        }

        false
    }
}

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 3