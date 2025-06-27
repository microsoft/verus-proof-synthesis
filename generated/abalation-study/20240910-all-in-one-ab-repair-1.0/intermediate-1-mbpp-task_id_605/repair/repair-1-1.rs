
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
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                index <= n,
                n >= 2,
        {
            if (n % index) == 0 {
                proof {
                    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)); // Ensure invariant holds.
                }
                return false;
            }
            index += 1;
        }
        proof {
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)); // Ensure invariant holds.
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp10gxaheo`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2
// Safe: False