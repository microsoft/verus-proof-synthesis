

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
            i >= 2, // Added to ensure i is always at least 2
    {
        assert(i >= 2);
        i += 1;
    }
}
}

//         assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]); // Added by AI
//   assertion failed: forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]

// Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: False