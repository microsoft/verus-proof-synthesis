
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() as int - i - 1],
{
    let length = v.len();
    if length == 0 {
        return;
    }
    let mut n: usize = 0;
    while n < length / 2
        invariant
            n <= length,
            forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length as int - 1 - j],
            forall|j: int| (j < 0 || j >= (length as int) - (n as int)) ==> v[j] == old(v)[j],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n += 1;
    }
    let length_ghost = length;
    assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost as int - 1 - k]);
}

}


//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False