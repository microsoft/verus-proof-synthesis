
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
    let mut index = 2;
    proof {
    }
    while index < n
        invariant
            2 <= index,
            2 <= index <= n,
            index <= n,
            index >= 2,
    {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2