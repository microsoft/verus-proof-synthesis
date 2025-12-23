
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
        // Starting assumption proof block
        proof {
            assert(n >= 2);
        }

        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if is_divisible(n as int, index as int) {
                // Proof that the exists condition for a divisor implies non-prime
                proof {
                    assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
                }
                return false;
            }
            index += 1;
        }

        // Concluding proof block
        proof {
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        }
        true
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnwq06pai`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False