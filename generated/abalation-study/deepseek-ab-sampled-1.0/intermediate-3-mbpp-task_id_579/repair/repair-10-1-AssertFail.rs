
use vstd::prelude::*;
fn main() {}

verus! {

fn while_loop(n: usize) 
    requires
        n >= 2,
{
    let mut i = 2;
    while i < n 
        invariant
            i <= n,
            n >= 2,
            i >= 2,
    {
        assert(i >= 2);
        i += 1;
    }
}

}


//                 assert(result.len() <= arr1.len() + arr2.len());
//   assertion failed: result.len() <= arr1.len() + arr2.len()

// Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: False