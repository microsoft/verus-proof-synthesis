use vstd::prelude::*;

fn main() {
    // verus does not support mod(%) operation on signed integers
    // so input should be unsigned integers

    // Write a function in Rust to check if the given integer is a prime number.

    assert!(!prime_num(0));
    assert!(!prime_num(1));
    assert!(prime_num(13));
    assert!(prime_num(7));
    assert!(!prime_num(1010));
}

verus! {

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
    {
        if ((n % index) == 0) {
            assert(is_divisible(n as int, index as int));
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
