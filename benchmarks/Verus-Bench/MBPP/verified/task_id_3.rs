use vstd::prelude::*;

fn main() {
    // verus does not support mod(%) operation on signed integers
    // so input should be unsigned integers

    //Write a function in Rust to identify non-prime numbers.
    assert!(is_non_prime(0));
    assert!(is_non_prime(1));
    assert!(!is_non_prime(2));
    assert!(is_non_prime(10));
    assert!(is_non_prime(35));
    assert!(!is_non_prime(37));
}

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
            2 <= index,
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
    {
        if ((n % index) == 0) {
            assert(is_divisible(n as int, index as int));
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
