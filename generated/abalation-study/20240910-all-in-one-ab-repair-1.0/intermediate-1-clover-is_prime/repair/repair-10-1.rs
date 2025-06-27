
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

        true
    }
}

### Tips For Running Verification:
1. **Command Line Usage**: Make sure you are running the Verus command correctly in your terminal.
2. **File Path**: Check that the file path provided to the Verus tool is correct and that only one file is being provided.

### Compilation Instructions:
To verify the code using Verus, you might use a command like:
sh
verus your_file_name.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpcf0ne2x1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False