
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
            (length - n as int) <= length as int,
            // For every element up to n, v[i] == old(v)[length - 1 - i]
            forall|i: int| 0 <= i < (n as int) ==> v[i] == old(v)[length - 1 - (i as usize)],
            // For every element beyond (length - n), v[i] == old(v)[i]
            forall|i: int| (n as int) + (length as int) - n as int <= i < length as int 
                ==> v[i] == old(v)[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n += 1;
    }
}

}


//             assert(forall|k: int| (length - (n as int)) <= k < length ==> v[k] == old(v)[k]);
//   assertion failed: forall|k: int| (length - (n as int)) <= k < length ==> v[k] == old(v)[k]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False