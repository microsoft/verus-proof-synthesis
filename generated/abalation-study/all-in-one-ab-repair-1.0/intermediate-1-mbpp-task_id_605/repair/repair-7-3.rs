
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
                forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
                n >= 2,
        {
            if is_divisible(n as int, index as int) {
                proof {
                    assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
                }
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp1e0mlcnn`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False