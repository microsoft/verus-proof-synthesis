
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
        assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
    }
    assert(exists|k: int| 2 <= k < index && is_divisible(n as int, k)); // Added by AI
    while index < n
        invariant
            2 <= index,
            2 <= index <= n,
            forall|k: int| 0 <= k < n ==> !is_divisible(n as int, k),
            index <= n,
            index >= 2,
            exists|k: int| 2 <= k < index && is_divisible(n as int, k), // Added by AI
    {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
        assert(exists|k: int| 2 <= k < index && is_divisible(n as int, k));
    }
    false
}

} // verus!


//     assert(exists|k: int| 2 <= k < index && is_divisible(n as int, k)); // Added by AI
//   assertion failed: exists|k: int| 2 <= k < index && is_divisible(n as int, k)

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2
// Safe: True