
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
    proof {
        assert(v.len() == length);
        assert(old(v).len() == length);
        // Assertion that the initial state satisfies the invariant conditions
        assert(foreach |k: int| 0 <= k < length ==> v[k] == old(v)[k]);
    }
    while n < length / 2
        invariant
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - 1 - i],
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - 1 - i],
            forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],
            forall|i: int| n <= i < length ==> v[i] == old(v)[i],
            forall|k: int| 0 <= k < n ==> v[k] == old(v)[length - 1 - k],
            forall|k: int|
                0 <= k < old(v).len() - (n as int) - 1 ==> v[k] == old(v)[old(v).len() - k - 1],
            forall|k: int| length - n < k < length ==> v[k] == old(v)[k],
            forall|k: int| old(v).len() - (n as int) - 1 <= k < old(v).len() ==> v[k] == old(v)[k],
            n <= length,
            n <= length / 2,
            old(v).len() == v.len(),
            v.len() == length,
            v.len() == old(v).len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
        proof {
            assert(foreach |i: int| 0 <= i < n ==> v[i] == old(v)[length - 1 - i]);
            assert(foreach |i: int| 0 <= i < n ==> v[i] == old(v)[length - 1 - i]);
            assert(foreach |i: int| n <= i < length - n ==> v[i] == old(v)[i]);
        }
    }
}

} // verus!


//             forall|k: int|
//                 0 <= k < old(v).len() - (n as int) - 1 ==> v[k] == old(v)[old(v).len() - k - 1],
//   None: forall|k: int|                 0 <= k < old(v).len() - (n as int) - 1 ==> v[k] == old(v)[old(v).len() - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: True