
use vstd::prelude::*;
fn main() {}
verus! {
    
#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        forall|i: int| 0 <= i < old(v).len() as int ==> v[i] == old(v)[old(v).len() as int - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],
            forall|j: int| (n as int <= j < (length - n) as int) ==> v[j] == old(v)[j],
            n <= length,
            v.len() == length,
            length == old(v).len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        assert(forall|k: int| 0 <= k < length as int ==> v[k] == old(v)[length as int - k - 1]);
    }
}

}


//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False