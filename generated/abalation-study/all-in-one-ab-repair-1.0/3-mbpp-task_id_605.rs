
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
        // Since n >= 2 by precondition, we don't need to check for n <= 1
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k as int),
        {
            if n % index == 0 {
                proof {
                    assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
                    assert(is_divisible(n as int, index as int));
                }
                return false;
            }
            index += 1;
        }
        proof {
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            // Since index goes from 2 to n-1, if we are here, then no divisor was found
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        }
        true
    }
}

// Score: (2, 0)
// Safe: False