
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
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
                // This invariant ensures that for all k in the range 2 to index, the number n is not divisible by k.
                // The array elements in this case are implicitly represented as checks for each k.
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                index <= n,
                n >= 2,
        {
            if ((n % index) == 0) {
                return false;
            }
            index += 1;
        }
        true
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpy5_s1b4h`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True