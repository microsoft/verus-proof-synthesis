
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
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length as int - i - 1],
            forall|i: int| 0 <= i < n ==> v[length as int - i - 1] == old(v)[i],
            forall|k: int| 0 <= k < v.len() ==> v[k] == old(v)[k], // Array v is never changed in this loop
            n <= length / 2,
            v.len() == length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}

} // verus!
