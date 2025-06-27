

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
            forall{j: int} (0 <= j < n as int) ==> v[j] == old(v)[(length - 1) - j],
            forall{j: int} (n as int <= j < (length - n) as int) ==> v[j] == old(v)[j],
            forall{j: int} ((length - n as int) <= j <= (length as int) - 1) ==> v[j] == old(v)[(length as int - 1) - j],
            n <= length,
            length == old(v).len(),
            v.len() == length,
            n as int <= (length / 2).to_int(), // Added to ensure termination
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
        proof {
            let n_ghost = n as int;
            assert(forall|k: int| 0 <= k < n_ghost + 1 ==> v[k] == old(v)[length - k - 1]); // Connecting the invariant through ghost state
        }
    }
    proof {
        let length_ghost = length as int;
        assert(length_ghost >= 0);
        for k in 0..(length / 2) {
            proof {
                assert(v[k as int] == old(v)[(length_ghost - 1) - k as int]);
            }
        }
        for k in (length / 2)..length {
            proof {
                assert(v[k as int] == old(v)[(length_ghost - 1) - k as int]);
            }
        }
    }
}
}

//         assert(forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]);
//   assertion failed: forall|k: int| 0 <= k < length_ghost as int ==> v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False