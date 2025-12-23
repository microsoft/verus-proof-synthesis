
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
    if n <= 1 {
        return true;
    }
    let mut found_divisor = false;
    let mut index = 2;
    while index < n
        invariant
            2 <= index <= n,
            !found_divisor == (forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k)),
            index <= n,
            n >= 2,
    {
        if (n % index) == 0 {
            found_divisor = true;
        }
        index += 1;
    }
    found_divisor
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphiq_h2jh`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False