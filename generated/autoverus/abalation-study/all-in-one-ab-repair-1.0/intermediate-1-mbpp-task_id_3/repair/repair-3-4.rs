
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
        proof {
            assert(result == true);
        }
        return true;
    }
    let mut index = 2;
    while index < n
        invariant
            2 <= index <= n,
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
            index <= n,
            n >= 2,
    {
        if (n % index == 0) {
            proof {
                assert(result == true);
            }
            return true;
        }
        index += 1;
    }
    proof {
        assert(result == false);
    }
    false
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnn0a6jg8`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False