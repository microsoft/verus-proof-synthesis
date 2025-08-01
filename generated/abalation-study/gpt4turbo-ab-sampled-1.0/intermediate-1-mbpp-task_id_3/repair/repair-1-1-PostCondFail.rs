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
    let ghost match_found = false;
    while index < n
        invariant
            !(exists|k: int| 2 <= k < index && is_divisible(n as int, k)),
            2 <= index <= n,
            // Since the array (or similar data structure) does not get modified in this loop, ensuring the invariant checks each potential divisor
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
            exists|k: int| match_found ==> 2 <= k < index && is_divisible(n as int, k),
    {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// failed this postcondition
//         result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
//             return true;
//   at this exit: return true
//   failed this postcondition: result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k))

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: True