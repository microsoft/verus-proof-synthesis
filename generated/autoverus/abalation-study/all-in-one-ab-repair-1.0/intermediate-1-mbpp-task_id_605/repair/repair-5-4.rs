
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
        let ghost old_result = exists|k: int| 2 <= k < n && is_divisible(n as int, k);
        
        if n <= 1 {
            proof {
                assert(!old_result);
                assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)); 
            }
            return false;
        }
        
        let mut index = 2;
        
        while index < n
            invariant
                2 <= index <= n,
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k) == !old_result,
                n >= 2,
        {
            if ((n % index) == 0) {
                return false;
            }
            index += 1;
        }
        
        proof {
            assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        }
        true
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmfw4imfg`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: True