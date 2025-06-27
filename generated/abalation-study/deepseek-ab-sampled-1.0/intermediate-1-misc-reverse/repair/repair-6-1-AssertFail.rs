
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
    let ghost mid = length / 2;
    while n < mid
        invariant
            forall|j: int| 0 <= j < n as int ==> v[j] == old(v)[length - j - 1],
            forall|j: int| n as int <= j < (length - n) as int ==> v[j] == old(v)[j],
            n <= mid,
            mid == length / 2,
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
        let length_ghost = length as int;
        let mid_ghost = mid as int;
        for k in 0.. length_ghost
        {
            if k < mid_ghost
            {
                assert(v[k] == old(v)[length_ghost - k - 1]);
            }
            else
            {
                if k > length_ghost - mid_ghost - 1
                {
                    assert(v[k] == old(v)[length_ghost - k - 1]);
                }
                else
                {
                    // Middle element in case of odd length
                    assert(v[k] == old(v)[k]);
                }
            }
        }
        assert(forall|k: int| 0 <= k < length_ghost ==> v[k] == old(v)[length_ghost - k - 1]);
    }
}


//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False