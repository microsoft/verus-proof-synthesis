
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
            index <= n,
            2 <= index,
    {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2