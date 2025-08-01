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
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],
            forall|i: int| length - n <= i < length ==> v[i] == old(v)[length - i - 1],
            forall|i: int| n <= i < v.len() - n ==> v[i] == old(v)[i],
            forall|i: int| v.len() - n <= i < v.len() ==> v[i] == old(v)[length - i - 1],
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - 1 - i],
            forall|i: int| 0 <= i < n ==> v[length - 1 - i] == old(v)[i],
            n <= length / 2,
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


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 6