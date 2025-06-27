
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
    let ghost mut revologue = 0;
    while n < length / 2
    invariant
        0 <= n <= length / 2,
        revologue == n as int,
        forall|i: int| 0 <= i < revologue ==> v[i] == old(v)[length - i - 1],
        forall|i: int| revologue <= i < length - revologue ==> v[i] == old(v)[i],
        n <= length,
        v.len() == length,
        v.len() == old(v).len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
        proof {
            let i = revologue;
            let j = length as int - i - 1;
            revologue = i + 1;
            assert(v[i] == old(v)[j]);
            assert(v[j] == old(v)[i]);
            assert(forall|k: int| 0 <= k <= revologue - 1 ==> v[k] == old(v)[length as int - k - 1]);
            assert(forall|k: int| revologue <= k < length as int - revologue ==> v[k] == old(v)[k]);
        }
    }
    proof {
        assert(forall|i: int| 0 <= i < old(v).len() as int ==> v[i] == old(v)[old(v).len() as int - i - 1]);
    }
}
}


//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True