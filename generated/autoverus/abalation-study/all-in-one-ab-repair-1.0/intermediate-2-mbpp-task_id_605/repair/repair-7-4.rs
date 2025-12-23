
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
            if is_divisible(n as int, index as int) {
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4s9gfu0r`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False