use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
            index <= n,
            n >= 2,
    {
        if ((n % index) == 0) {
            proof {
                assert(is_divisible(n as int, index as int)); // Added by AI, for assertion fail
                assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
            }
            return false;
        }
        index += 1;
    }
    true
}

}

//                 assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k)); // Added by AI
//   assertion failed: exists|k: int| 2 <= k < n && is_divisible(n as int, k)

// Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True