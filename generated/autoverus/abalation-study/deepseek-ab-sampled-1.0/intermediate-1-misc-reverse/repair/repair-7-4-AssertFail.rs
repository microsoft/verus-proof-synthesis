

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
    let ghost initial_v = old(v);
    while n < length / 2
        invariant
            forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],
            forall|j: int| (n as int <= j < (length - n) as int) ==> v[j] == old(v)[j],
            n <= length / 2,
            length == old(v).len(),
            v.len() == length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
        proof {
            // Maintain the invariant that for each n, the elements at positions n and length - n -1 have been swapped correctly
            let swapped_n: int = n as int - 1;
            assert(v[swapped_n] == old(v)[length as int - 1 - swapped_n]);
        }
    }
    // After the loop, ensure that the entire array has been reversed
    proof {
        let length_ghost = length as int;
        assert(forall|k: int| 0 <= k < length_ghost / 2 ==> v[k] == old(v)[length_ghost - k - 1]);
        assert(forall|k: int| length_ghost / 2 <= k < length_ghost ==> v[k] == old(v)[length_ghost - k - 1]);
        assert(forall|k: int| 0 <= k < length_ghost ==> v[k] == old(v)[length_ghost - k - 1]);
    }
}
}

//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True