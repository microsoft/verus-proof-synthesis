
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
            return false;
        }
        
        let mut index = 2;
        
        while index * index <= n
            invariant
                2 <= index <= n + 1,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if (n % index) == 0 {
                proof {
                    assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
                }
                return false;
            }
            index += 1;
        }
        
        proof {
            assert(forall|k: int| 2 <= k * k <= n ==> k < n ==> !is_divisible(n as int, k));
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)); // New proof assert
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpw7ylrxvv`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 6
// Safe: False