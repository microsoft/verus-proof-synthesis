

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
            forall|j: int| (n as int <= j <= (length - n - 1) as int) ==> v[j] == old(v)[j],
            n <= length,
            length == old(v).len(),
            v.len() == length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
        proof {
            let current_n = n - 1;
            assert(forall|j: int| 0 <= j <= current_n as int ==>
                v[j] == old(v)[length - j - 1]);
            assert(forall|j: int| (current_n as int + 1 <= j <= (length - current_n - 2) as int) ==>
                v[j] == old(v)[j]);
        }
    }
    proof {
        let length_ghost = length;
        assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
    }
}

}

//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True