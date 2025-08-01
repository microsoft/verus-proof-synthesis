

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],
            forall|j: int| (n as int <= j < (length - n) as int) ==> v[j] == old(v)[j],
            forall|j: int| (j >= (length - n) as int) ==> v[j] == old(v)[(length - 1) - (j - (length - n))] ,
            n <= length,
            length == old(v).len(),
            v.len() == length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        let length_ghost = length as int;
        assert(forall|k: int| 0 <= k < length_ghost ==> 
                   v[k] == old(v)[length_ghost - k - 1]) by {
            // For any k in [0, length_ghost),
            // if k < len / 2, it's been swapped in the loop
            // if k >= len / 2, it's already in the correct position
        };
    }
}
}

//         assert(forall|k: int| 0 <= k < length_ghost ==> 
//                    v[k] == old(v)[length_ghost - k - 1]) by {
//   assertion failed: forall|k: int| 0 <= k < length_ghost ==>                     v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True