
use vstd::prelude::*;
fn main() {}
verus! {

// This function is unchecked since we purposely break the loop_isolation contract for this example.
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
    let mut index = 2;
    while index < n
        invariant
            2 <= index <= n,
            // This invariant ensures that for all k in the range 2 to index, the number n is not divisible by k.
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
    {
        if is_divisible(n as int, index as int) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpphotxum7`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False