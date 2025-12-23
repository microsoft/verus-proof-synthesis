
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    let mut found_divisor = false; // Added to help with postcondition
    let mut index = 2;
    while index < n
        invariant
            2 <= index <= n,
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
            index <= n,
            n >= 2,
            found_divisor == (exists|k: int| 2 <= k < index && is_divisible(n as int, k)), // Added to ensure the loop correctly maintains the postcondition
    {
        if (n % index) == 0 {
            found_divisor = true; // Found a divisor in range, updating the flag
            break;
        }
        index += 1;
    }
    found_divisor
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpjm1ni0wv`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: False