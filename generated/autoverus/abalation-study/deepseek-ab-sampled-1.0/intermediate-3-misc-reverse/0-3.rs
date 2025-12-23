

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
            n <= length,
            v.len() == old(v).len(),
            old(v)[( 0..length ) as int] == v[0..length].subrange(0, length as int),
            forall |k: int| 0 <= k < n ==> v[k] == old(v)[length as int -1 -k],
            forall |k: int| n <= k < length ==> v[k] == old(v)[k],
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3