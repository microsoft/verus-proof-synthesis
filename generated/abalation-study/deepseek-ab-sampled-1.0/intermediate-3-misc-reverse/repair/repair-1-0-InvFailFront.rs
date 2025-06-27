

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
    ghost let old_v = old(v);
    ghost let len = length;

    while n < length / 2
        invariant
            n <= len / 2,
            v.len() == len,
            forall|i: int| 0 <= i < (n + 1) as int ==> v[i] == old_v[len - 1 - i as int],
            forall|i: int| (len - n - 1) <= i < len - n ==> v[i] == old_v[i],
    {
        let x = v[n];
        let y = v[len - 1 - n];
        v.set(n, y);
        v.set(len - 1 - n, x);
        n += 1;
    }
}
}

//             forall|i: int| 0 <= i <= n ==> v[i] == old(v)[length - 1 - i],
//   None: forall|i: int| 0 <= i <= n ==> v[i] == old(v)[length - 1 - i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False