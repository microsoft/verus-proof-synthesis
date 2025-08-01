

use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let old_v = old(v);
    let length = old_v.len();
    let mut n: usize = 0;
    while (n < length / 2)
        invariant
            n <= length / 2,
            0 < length < 1000,
            v.len() == old_v.len(),
            forall |k: int| 0 <= k < n ==> v[k] == old_v[length - 1 - k as int],
            forall |k: int| n <= k < length - n ==> v[k] == old_v[k as int],
            n as int + length / 2 as int < length,
    {
        if n < length / 2 {
            let index = length - 1 - n;
            if index != n {
                let x = v[n];
                let y = v[index];
                v.set(n, y);
                v.set(index, x);
            }
        }
        n = n + 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1