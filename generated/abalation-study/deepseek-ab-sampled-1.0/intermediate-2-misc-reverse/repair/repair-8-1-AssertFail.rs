

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let old_v = old(v);
    let len = v.len();
    let mut n = 0;
    while n < len / 2
    invariant
        0 <= n <= len / 2,
        forall|i: int| 0 <= i < n ==> v[i] == old_v[len - i - 1],
        forall|i: int| n <= i < len - n ==> v[i] == old_v[i],
    {
        let x = v[n];
        let y = v[len - 1 - n];
        v.set(n, y);
        v.set(len - 1 - n, x);
        n += 1;
        proof {
            let i = n as int;
            let j = (len as int) - i - 1;
            assert(v[i as u64] == old_v[j as u64]);
            assert(v[j as u64] == old_v[i as u64]);
        }
    }
    proof {
        let len_int = len as int;
        for i in 0..len_int
            requires
                0 <= i < len_int,
            ensures
                v[i] == old_v[len_int - i - 1],
        {
            if (i as u64) < len / 2 {
                let n_i = i as u64;
                assert(v[n_i] == old_v[len - n_i - 1]);
            } else {
                let n_i = i as u64;
                assert(v[n_i] == old_v[n_i]);
                assert(old_v[n_i] == old_v[len - (len - n_i) - 1]);
            }
        }
        assert(forall|i: int| 0 <= i < old_v.len() ==> v[i] == old_v[old_v.len() - i - 1]);
    }
}
}

//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False