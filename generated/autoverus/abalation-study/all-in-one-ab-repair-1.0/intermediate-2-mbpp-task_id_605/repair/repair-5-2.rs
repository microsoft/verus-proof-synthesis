
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
        while (index as u64) < n
            invariant
                2 <= index <= n as int,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if is_divisible(n as int, index) {
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



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa_ompyc3`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False