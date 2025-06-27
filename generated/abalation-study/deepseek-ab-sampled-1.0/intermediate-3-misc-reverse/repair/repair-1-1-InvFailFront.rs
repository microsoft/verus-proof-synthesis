

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
            n <= length,
            n <= length / 2,
            v.len() == old(v).len(),
            forall|i: int|
                0 <= i < n ==>
                    v[i] == old(v)[length - 1 - i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}
}

//             forall|i: int| 0 <= i <= n ==> v[i] == old(v)[length - 1 - i],
//   None: forall|i: int| 0 <= i <= n ==> v[i] == old(v)[length - 1 - i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False