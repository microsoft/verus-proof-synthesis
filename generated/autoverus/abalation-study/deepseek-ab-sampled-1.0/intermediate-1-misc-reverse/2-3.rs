

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
            lenght > 0,
            n <= (length / 2) as usize,
            0 <= (length - 1 - n) < length,
            for any j: int, 0 <= j < n => v[j] == old(v)[(length as int) - 1 - j],
    {
        let x = v.get(n);
        let y = v.get(length - 1 - n);

        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1