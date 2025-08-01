
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
    let ghost original_n = n; 
    
    if n <= 1 {
        // This block will never be executed due to the precondition n >= 2.
        return true;
    }
    let mut index = 2;
    while index < n
        invariant
            2 <= index <= n,
            forall|k: int| 2 <= k < index ==> !is_divisible(original_n as int, k),
            n >= 2,
    {
        if ((n % index) == 0) {
            proof {
                assert(is_divisible(original_n as int, index));
                assert(exists|k: int| 2 <= k < n && is_divisible(original_n as int, k));
            }
            return true;
        }
        index += 1;
        proof {
            assert(forall|k: int| 2 <= k < index ==> !is_divisible(original_n as int, k));
        }
    }
    return false;
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpbnmf18o5`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False