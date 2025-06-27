
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
        let n_int = n as int;

        let mut index = 2;
        while index < n_int
            invariant
                2 <= index <= n_int,
                forall|k: int| 2 <= k < index ==> !is_divisible(n_int, k),
                index <= n_int,
                n >= 2,
        {
            if is_divisible(n_int, index) {
                return false;
            }
            index += 1;
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5x_e2dt2`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False