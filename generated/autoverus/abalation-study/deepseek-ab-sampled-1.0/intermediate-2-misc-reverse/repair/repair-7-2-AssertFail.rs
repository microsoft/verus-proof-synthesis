

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
        0 <= n <= length / 2,
        forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],
        forall|i: int| 0 <= i <= n ==> v[length - i - 1] == old(v)[i],
        forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],
        n <= length,
        n <= length / 2,
        v.len() == length,
        v.len() == old(v).len(),
        // Added loop invariant to connect the reversed parts
        forall|i: int, j: int| 0 <= i < j < length ==> if j < n then v[i] == old(v)[length - i - 1] else if i > length - j - 1 then v[i] == old(v)[length - i - 1] else v[i] == old(v)[i]
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
        proof {
            let i = n as int;
            let j = (length as int) - i - 1;
            assert(v[i as int] == old(v)[j as int]);
            assert(v[j as int] == old(v)[i as int]);
            // Update the ghost state to reflect the swap
            assert(forall|k: int| 0 <= k <= i ==> v[k] == old(v)[length - k - 1]);
            assert(forall|k: int| length - i - 1 <= k < length ==> v[k] == old(v)[length - k - 1]);
        }
    }
    proof {
        // After the loop, connect the entire vector using the strengthened invariants
        assert(forall|i: int| 0 <= i < n as int ==> v[i] == old(v)[length - i - 1]);
        assert(forall|i: int| 0 <= i < n as int ==> v[length - i - 1] == old(v)[i]);
        assert(forall|i: int| n as int <= i < length - n as int ==> v[i] == old(v)[i]);
        // Combine to show the entire vector is reversed
        assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
    }
}
}

//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False