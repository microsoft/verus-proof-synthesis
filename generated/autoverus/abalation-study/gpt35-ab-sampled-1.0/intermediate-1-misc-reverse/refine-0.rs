
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
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[old(v).len() - i - 1],
            forall|i: int|
                length as usize / 2 <= i < old(v).len() as usize ==> v[i] == old(v)[old(
                    v,
                ).len() as usize - i - 1],
            forall|i: int| n <= i < old(v).len() - n ==> v[i] == old(v)[i],
            n <= length / 2,
            v.len() == old(v).len(),
            // Loop invariant from function precondition:
            forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}

} // verus!
