
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
            (exists|k: int| 2 <= k < index && is_divisible(n as int, k)),
            2 <= index,
            2 <= index <= n,
            forall|k: int| 0 <= k < n ==> !is_divisible(n as int, k), // Array x is not modified in the loop, as there is no x.set(). Hence, the invariant is adjusted to cover every element in the array.
            index <= n,
            index >= 2,
            n >= 2,
            2 <= index < n && is_divisible(n as int, 2),
    {
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
