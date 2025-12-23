
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
                n >= 2,
        {
            if (n % index) == 0 {
                return false;
            }
            index += 1;
        }
        true
    }
} 


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpv4ibi0k3`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False