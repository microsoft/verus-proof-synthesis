

use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while (n < length / 2)
        invariant 
            n <= length / 2,
            v.len() == old(v).len(),
            forall |k: int| 0 <= k < n as int ==> v[k] == old(v)[length as int - k - 1],
            forall |k: int| 0 <= k < n as int ==> v[length as int - k - 1] == old(v)[k],
            forall |k: int| n <= k < length / 2 ==> v[k] == old(v)[k],
            forall |k: int| n <= k < length / 2 ==> v[length as int - k - 1] == old(v)[length as int - k - 1],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1