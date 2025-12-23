
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


//     assert(max_val - min_val <= i32::MAX);
//   assertion failed: max_val - min_val <= i32::MAX

// Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: False