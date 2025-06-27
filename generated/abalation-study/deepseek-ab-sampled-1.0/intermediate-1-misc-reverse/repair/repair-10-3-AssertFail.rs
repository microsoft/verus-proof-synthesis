
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
            forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[(length - 1) - j],
            forall|j: int| (n as int <= j < (length - n) as int) ==> v[j] == old(v)[j],
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
        for k in 0..length {
            if k < (length / 2) {
                // Elements swapped in the loop
                proof {
                    assert(v[k] == old(v)[length - 1 - k]);
                }
            } else if k > (length / 2 - 1) {
                // Elements that may remain in place for even lengths
                proof {
                    assert(v[k] == old(v)[length - 1 - k]);
                }
            } else {
                // Middle element in odd lengths (remains in place)
                proof {
                    assert(v[k] == old(v)[length - 1 - k]);
                }
            }
        }
        assert(forall|k: int| 0 <= k < length ==> 
                   v[k] == old(v)[length - 1 - k]);
    }
}
}


//         assert(forall|k: int| 0 <= k < length_ghost ==> 
//                    v[k] == old(v)[length_ghost - k - 1]) by {
//   assertion failed: forall|k: int| 0 <= k < length_ghost ==>                     v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True