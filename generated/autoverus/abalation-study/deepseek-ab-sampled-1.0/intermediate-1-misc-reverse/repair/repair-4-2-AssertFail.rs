
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
            // Added invariants to strengthen the proof
            old(v).len() == length,
            n as int >= 0,
            n as int + n as int <= length as int,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        let length_ghost = length;
        assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]
            by {
                // Using SCHEME ESTABLISH to apply the loop invariants
                match k >= 0 && k < length_ghost as int {
                    true => apply_spec!! reverse.Weaken 1 k;
                    false => contradiction
                }
            })
    }
}


//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False