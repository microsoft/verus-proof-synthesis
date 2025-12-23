
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
        let mut index = 2;
        
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if ((n % index) == 0) {
                proof {
                    assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
                }
                return false;
            }
            index += 1;
        }
        
        proof {
            // At this point, index == n and the loop has verified all k in the range from 2 to n-1
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpc6wvil0t`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False