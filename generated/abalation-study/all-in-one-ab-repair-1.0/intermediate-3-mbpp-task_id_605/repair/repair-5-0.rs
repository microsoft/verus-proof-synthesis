
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
        let mut proof_check = true; // Added by AI: to pass verification for return in if block
        if n <= 1 {
            return false;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                proof_check, // Added by AI: ensure we still check the proof
        {
            if ((n % index) == 0) {
                proof_check = false; // Added by AI: to record reason for break
                break;
            }
            index += 1;
        }
        proof { // Added by AI: to ensure the postcondition
            if proof_check {
                assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
            }
        }
        proof_check // use proof_check to determine result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp1z7a4bzi`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: False