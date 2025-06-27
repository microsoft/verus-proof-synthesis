
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
        if n <= 1 {
            return false;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if ((n % index) == 0) {
                return false;
            }
            index += 1;
            proof {
                // We need to ensure the invariant still holds after `index` is incremented.
                assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));

                // Every `k` between 2 and `index-1` does not divide `n`,
                // and since `index` has been incremented by 1, this still holds.
            }
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpoog4ljle`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True