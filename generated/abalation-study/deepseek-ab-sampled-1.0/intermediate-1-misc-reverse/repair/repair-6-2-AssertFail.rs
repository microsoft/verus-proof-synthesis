
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
    let ghost mut iter = 0;
    while n < length / 2
        invariant
            iter == n,
            forall|j: int| (0 <= j < iter as int) ==> v[j] == old(v)[length - j - 1],
            forall|j: int| (iter as int <= j < (length - iter) as int) ==> v[j] == old(v)[j],
            n <= length,
            length == old(v).len(),
            v.len() == length,
    {
        ghost iter = iter + 1;
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        let length_ghost = length;
        // Use the loop invariants to split the proof into two parts:
        // 1. For all k < iter, v[k] == old(v)[length - k - 1]
        // 2. For all k >= iter, v[k] == old(v)[k] if k >= length - iter
        assert ******************************************************************************/

        forall|k: int|
        if 0 <= k < (n as int) {
            v[k] == old(v)[length_ghost - k - 1]
        } else if (n as int) <= k < (length_ghost - n as int) {
            v[k] == old(v)[k]
        } else {
            true
            // These cases cover all possibilities as the loop invariant ensures the first
            // `n` elements are reversed and the remaining are unchanged until `length - n`
        };

        // Since the loop has completed, n == length / 2. For each k, the properties hold:
        // - If k < length / 2, it was processed and reversed.
        // - If k >= length / 2, it mirrors the first half and thus also satisfies the reversed condition.
        assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
    }
}
}


//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False