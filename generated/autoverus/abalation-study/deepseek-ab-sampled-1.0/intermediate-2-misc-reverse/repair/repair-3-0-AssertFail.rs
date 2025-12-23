
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
    if length == 0 {
        return;
    }
    let mut n: usize = 0;
    while n < length / 2
        invariant
            0 <= n <= length / 2,
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[(length as int) - i - 1],
            forall|i: int| n <= i < (length as int) - n ==> v[i] == old(v)[i],
            v.len() == length,
            v.len() == old(v).len(),
        {
            // Swap elements at positions n and length - 1 - n
            let x = v[n];
            let y = v[length - 1 - n];
            v.set(n, y);
            v.set(length - 1 - n, x);

            // Prove that the first 'n + 1' elements are correctly reversed
            proof {
                assert(forall|i: int| 0 <= i < n + 1 ==> v[i] == old(v)[(length as int) - i - 1]);
                // The middle segment remains unchanged
                assert(forall|i: int| (n + 1) <= i < (length as int) - (n + 1) ==> v[i] == old(v)[i]);
            }

            n += 1;
        }
    // After loop, ensure the entire vector is reversed
    proof {
        assert(forall|i: int| 0 <= i < (length as int) ==> v[i] == old(v)[(length as int) - i - 1]);
    }
}
}


//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False