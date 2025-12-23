

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
            v.len() == length,
            forall |j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],
            forall |j: int| (j >= n as int && j < length as int - n as int) ==> v[j] == old(v)[j],
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
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1