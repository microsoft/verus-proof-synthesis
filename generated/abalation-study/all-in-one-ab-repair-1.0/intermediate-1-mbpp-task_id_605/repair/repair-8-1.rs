
use vstd::prelude::*;
fn main() {}

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
            return false; // should never hit due to precondition n >= 2
        }

        let mut index = 2;

        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        {
            if (n % index == 0) {
                return false;
            }
            index += 1;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prime() {
        assert_eq!(prime_num(2), true);
        assert_eq!(prime_num(3), true);
        assert_eq!(prime_num(4), false);
        assert_eq!(prime_num(5), true);
        assert_eq!(prime_num(9), false);
        assert_eq!(prime_num(17), true);
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpat9m1ovz`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False