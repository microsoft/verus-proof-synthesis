
use vstd::prelude::*;
fn main() {}
verus! {

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            0 <= n <= length / 2,
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],
            forall|i: int| 0 <= i < n ==> v[i]@ == old(v)[length - 1 - i as int],
            forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],
            forall|i: int| n <= i < length - n ==> v[i]@ == old(v)[i as int],
            n <= length,
            n <= length / 2,
            v.len() == length,
            forall|k: int| 0 <= k < (n as int) ==> v[k] == old(v)[(length - 1 - k) as int],
            v.len() == old(v).len(),
            v.len() == old(v).len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}

} // verus!
