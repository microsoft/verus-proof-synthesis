
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
            proof {
                assert(!forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)); // This is trivially true due to the premise n >= 2
            }
            return false;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if ((n % index) == 0) {
                proof {
                    assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
                }
                return false;
            }
            index += 1;
        }
        proof {
            assert(forall|k: int| 2 <= k <= index ==> !is_divisible(n as int, k));
        }
        return true;
    }
}

Make sure that you are running your build processes correctly and no extra parameters are causing issues. If you're invoking Verus, ensure you have the correct settings ready. Here is a generic way to invoke verus in the command line:

bash
verus filename.rs

Or if inside a cargo project with the necessary dependencies correctly laid out.

bash
cargo verus run


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpt5g5_unj`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False