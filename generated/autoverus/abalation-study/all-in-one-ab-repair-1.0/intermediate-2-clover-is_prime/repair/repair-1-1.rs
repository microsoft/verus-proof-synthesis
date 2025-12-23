
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]

    spec fn divides(factor: nat, candidate: nat) -> bool {
        candidate % factor == 0
    }

    spec fn is_prime(candidate: nat) -> bool {
        &&& 1 < candidate
        &&& forall |factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
    }

    fn test_prime(candidate: u64) -> (result: bool)
        requires
            1 < candidate,
        ensures
            result == is_prime(candidate as nat),
    {
        let mut factor: u64 = 2;
        while factor < candidate
            invariant
                1 < candidate,
                2 <= factor <= candidate,
                forall |f: nat| 2 <= f < factor ==> !divides(f, candidate as nat),
                forall |i: u64| 2 <= i < factor ==> !(divides(i as nat, candidate as nat)),
        {
            if candidate % factor == 0 {
                return false;
            }
            factor = factor + 1;
        }
        true
    }
} // verus!

Here's a step-by-step guide you might want to ensure the compilation process:
1. Ensure you only compile this single file without additional filenames.
2. Invoke the appropriate Verus command to run your code, and ensure no lingering filenames/scripts are being invoked together.

Recheck the command being used. Typically, it should be something like this:
sh
verus-verifier <source_file>


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpb_uzbnz9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False