
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
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                index <= n,
                n >= 2,
        {
            if (n % index) == 0 {
                return false;
            }
            index += 1;
            proof {
                // The invariant forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k) holds here because we checked n % index before incrementing
                assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            }
        }
        true
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpor0y0awe`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False