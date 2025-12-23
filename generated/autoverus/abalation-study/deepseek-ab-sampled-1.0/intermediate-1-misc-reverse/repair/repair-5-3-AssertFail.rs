
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
            // Ensure that the first `n` elements are correctly reversed
            forall|j: int| 0 <= j < n as int ==> v[j] == old(v)[(length - 1 - j) as int],
            // Ensure that the middle part hasn't been touched yet
            forall|j: int| n as int <= j < (length - n) as int ==> v[j] == old(v)[j],
            // Ensure that `n` doesn't exceed half the length
            n <= length,
            // Ensure that the length is maintained
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
        let length_ghost = length;
        // Assert that the entire vector is reversed by iterating over all possible indices
        for k in 0..length_ghost
            ensures
                forall|i: int| 0 <= i < k as int ==> v[i] == old(v)[(length_ghost - 1 - i) as int],
                0 <= k < length_ghost + 1,
        {
            assert(v[k] == old(v)[(length_ghost - 1 - k) as int]);
        }
    }
}
}


//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False