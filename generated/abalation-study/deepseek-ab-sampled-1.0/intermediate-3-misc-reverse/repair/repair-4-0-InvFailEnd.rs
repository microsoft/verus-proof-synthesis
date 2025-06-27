
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
            old(v).len() == length,
            v.len() == length,
            n <= length / 2,
            (n as int) <= length as int,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        
        proof {
            assert(forall|k: int| 0 <= k < (n as int) ==> v[k] == old(v)[length - 1 - k]);
            assert(forall|k: int| (n as int) <= k < length - (n as int) ==> v[k] == old(v)[k]);
            assert(forall|k: int| (length - (n as int)) <= k < length ==> v[k] == old(v)[k]);
        }
        
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}

} // verus!


//             forall|k: int| 0 <= k < (n as int) ==> v[k] == old(v)[length - 1 - k]
//             &&
//             forall|k: int| (n as int) <= k < length - (n as int) ==> v[k] == old(v)[k]
//             &&
//             forall|k: int| (length - (n as int)) <= k < length ==> v[k] == old(v)[k],
//   None: forall|k: int| 0 <= k < (n as int) ==> v[k] == old(v)[length - 1 - k]             &&             forall|k: int| (n as int) <= k < length - (n as int) ==> v[k] == old(v)[k]             &&             forall|k: int| (length - (n as int)) <= k < length ==> v[k] == old(v)[k]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True