
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
            proof {
                assert(!result);
                assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)); 
            }
            return false;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                // This invariant ensures that for all k in the range 2 to index, the number n is not divisible by k.
                // The array elements in this case are implicitly represented as checks for each k.
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if ((n % index) == 0) {
                proof {
                    assert(result == false);
                }
                return false;
            }
            index += 1;
        }
        proof {
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        }
        true
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpyz3m0spw`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True