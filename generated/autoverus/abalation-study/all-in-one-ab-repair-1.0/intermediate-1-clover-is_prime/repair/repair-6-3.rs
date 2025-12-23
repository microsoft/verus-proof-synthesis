
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn divides(factor: nat, candidate: nat) -> bool {
        candidate % factor == 0
    }

    spec fn is_prime(candidate: nat) -> bool {
        &&& 1 < candidate
        &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
    }

    fn test_prime(candidate: u64) -> bool
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
                forall|f: nat| 2 <= f < factor ==> !divides(f, candidate as nat),
        {
            if candidate % factor == 0 {
                return false;
            }
            factor = factor + 1;
        }

        proof {
            assert(forall|f: nat| 2 <= f < candidate ==> !divides(f, candidate as nat));
        }

        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpj4mkreod`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True