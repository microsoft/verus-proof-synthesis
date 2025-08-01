
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
            result == (forall|k: int| 2 <= k < n as int ==> !is_divisible(n as int, k)),
    {
        if false {
            // The condition `n <= 1` can never be true due to `requires n >= 2`
            return false;
        }
        let mut index = 2;
        while (index as u64) < n
            invariant
                2 <= index <= n as int,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if (n % (index as u64)) == 0 {
                return false;
            }
            index += 1;
            proof {
                assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            }
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpeay7yywb`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 3
// Safe: False