

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
            n >= 0,
            n <= (length / 2),
            v.len() == length,
            forall |i: int| i < n
                ==> v[i] == old(v)[length - i - 1]
                && v[length - i - 1] == old(v)[i],
            forall |i: int| i >= n
                ==> v[i] == old(v)[i]
                && v[length - i - 1] == old(v)[length - i - 1],
            v.len() / 2 == length / 2,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1