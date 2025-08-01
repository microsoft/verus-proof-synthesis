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
            2 <= n,
            2 <= n, // Repeated invariant
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
            index <= n,
            true,
    {
        if ((n % index) == 0) {
            proof {
                assert(is_divisible(n as int, ( index ) as int)); // Added by AI
            }
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// Score: (2, 0)
// Safe: True