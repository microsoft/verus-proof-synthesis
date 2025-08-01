
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
        let n_int = n as int; // add ghost variable for verification purposes

        let mut index = 2;

        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n_int, k),
                n >= 2,
        {
            if is_divisible(n_int, index) {
                proof {
                    assert(forall|k: int| 2 <= k < index ==> !is_divisible(n_int, k));
                }
                return false;
            }
            index += 1;
        }

        proof {
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n_int, k));
            assert(forall|k: int| 2 <= k < n_int ==> !is_divisible(n_int, k)); // New proof assertion
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphppqkjrl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False