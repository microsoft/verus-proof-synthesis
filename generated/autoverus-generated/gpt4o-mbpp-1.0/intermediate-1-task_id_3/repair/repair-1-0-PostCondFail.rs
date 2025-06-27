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
    while index < n
        invariant
            2 <= index <= n,
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
            forall|j: int| 2 <= j < index ==> !is_divisible(n as int, j),
            index <= n,
            n >= 2,
    {
        if ((n % index) == 0) {
            proof {
                assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k)); // Added by AI
            }
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

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True