
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
            return false;
        }
        let mut index = 2;
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if (n % index == 0) {
                return false;
            }
            index += 1;
            proof {
                assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
            }
        }
        true
    }
}

If you're still having trouble with `multiple input filenames provided`, you may have to check the way you're running the tool. Ensure you're using the correct command for Verus and Rust invocations, such as:

verus <your_file.rs>


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpq5dwvijh`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False