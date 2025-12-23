

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
            length == old(v).len(),
            n <= length / 2,
            (n < length / 2) ==> 2 * n < length,
            forall |k: int| 0 <= k < i32::try_from(n).unwrap() == Ok(let k) ==> v[k as usize] == old(v)[(length - 1 - k) as usize],
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