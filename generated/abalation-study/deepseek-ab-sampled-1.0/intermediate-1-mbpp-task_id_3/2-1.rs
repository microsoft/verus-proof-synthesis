

use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
        forall |k: int| 2 <= k < n ==> k >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    if n <= 1 {
        return true;
    }
    let mut index = 2;
    while index < n
        invariant
            index >= 2,
            index <= n,
            forall |k: int| 2 <= k < index ==> (n as int) % k != 0,
        // Additional invariants for clarity and verification
        //
        // Ensuring that the index is always within the valid range [2, n)
            index <= n,
        // Ensuring that for all previous indices, none divided n
            forall |k: int| 2 <= k < index && k < n ==> (n as int) % k != 0,
    {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1