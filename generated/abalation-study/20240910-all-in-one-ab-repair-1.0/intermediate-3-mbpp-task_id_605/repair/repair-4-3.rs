
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
        if n == 2 {
            return true;
        }
        let mut index = 2;
        while index <= n / 2
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                index <= n / 2,
                n >= 2,
        {
            if ((n % index) == 0) {
                return false;
            }
            index += 1;
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpple85uaw`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False