
use vstd::prelude::*;
fn main() {}

verus! {
    // Specification that checks if a number is divisible by another
    spec fn is_divisible(n: int, divisor: int) -> bool {
        (n % divisor) == 0
    }

    // Function to check if a number `n` is prime
    fn prime_num(n: u64) -> (result: bool)
        requires
            n >= 2,
        ensures
            result == (forall|k: int| 2 <= k < n as int ==> !is_divisible(n as int, k)),
    {
        if n == 2 {
            return true;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if (n % index) == 0 {
                return false;
            }
            index += 1;
        }

        proof {
            // Proof block for post condition when the loop completes
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k - 1));
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp70kqrsvz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False