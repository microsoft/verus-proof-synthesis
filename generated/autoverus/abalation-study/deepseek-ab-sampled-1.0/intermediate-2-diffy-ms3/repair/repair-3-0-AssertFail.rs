
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
        assert(i >= 2); // Added explicit check to enforce i >= 2
        i += 1;
    }
}

}


//             assert(forall|k: usize| k < i ==> sum[0] == old(sum)[0] + a[(k) as int]);
//   assertion failed: forall|k: usize| k < i ==> sum[0] == old(sum)[0] + a[(k) as int]

// Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: False