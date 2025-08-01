
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
            2 <= index <= n,
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
            // This invariant is modified to cover every element in the range 2 to index
            forall|j: int| 2 <= j < index ==> !is_divisible(n as int, j),
            index <= n,
            n >= 2,
    {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
