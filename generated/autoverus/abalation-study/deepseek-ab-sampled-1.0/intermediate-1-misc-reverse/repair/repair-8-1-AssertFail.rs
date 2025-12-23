
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
        let length_ghost = length;
        // Establish that all elements have been correctly reversed.
        assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
        proof {
            // Show that for every k, after the loop, the element at k is the reversed element.
            show forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1];
            intro k;
            show 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1];
            intro h;
            // Use the loop invariant to establish that each swap correctly places elements.
            if k < n as int || k >= (length - n) as int {
                contradiction!();
            } else {
                // Each element from n to length - n - 1 has been swapped to its correct reversed position.
                split!();
            }
        }
    }
}

}


//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False