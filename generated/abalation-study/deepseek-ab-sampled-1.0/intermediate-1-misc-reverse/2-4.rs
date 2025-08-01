

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

    while n < length / 2
        invariant
            n <= length / 2,
            forall |k: int| 0 <= k < n as int ==> v[k] == old(v)[(length - 1 - k) as int],
            forall |k: int| n as int <= k < (length - n) as int ==> v[k] == old(v)[k as int],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 8