
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_divisible(n: int, divisor: int) -> bool {
        (n % divisor) == 0
    }

    fn is_non_prime(n: u64) -> (result: bool)
        requires
            n >= 2,
        ensures
            result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
    {
        if n <= 1 {
            return true;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if ((n % index) == 0) {
                return true;
            }
            index += 1;
        }
        false
    }
} // verus!

### Key Points:
1. **Invariants and Loop Conditions**: Ensure the invariants hold true before and after the loop.
2. **Check Divisibility**: We check the divisibility and update accordingly.

Given your error message is about multiple input filenames, it might be a scenario outside the context of the verification tool. Ensure:
- You're using the correct command to run your Verus tool.
- No extra parameters or filenames are passed accidentally.

### Example Command to Run Verus
Make sure your environment is set up correctly and use a command similar to:

sh
verus --output /tmp/outputfile /path/to/your_file.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpo90py5ac`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False