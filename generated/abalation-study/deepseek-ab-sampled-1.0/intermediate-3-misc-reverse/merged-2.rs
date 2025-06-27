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
            forall|i: int| 0 <= i <= n ==> v[i] == old(v)[length - 1 - i],
            forall|i: int| n <= i < length ==> v[i] == old(v)[i],
            forall|k: int| 0 <= k < n ==> v[k] == old(v)[length - 1 - k],
            forall|k: int|
                0 <= k < old(v).len() - (n as int) - 1 ==> v[k] == old(v)[old(v).len() - k - 1],
            forall|k: int| length - n < k < length ==> v[k] == old(v)[k],
            forall|k: int| old(v).len() - (n as int) - 1 <= k < old(v).len() ==> v[k] == old(v)[k],
            n <= length,
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - 1 - i],
            forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],
            n <= length / 2,
            v.len() == length,
            v.len() == old(v).len(),
            old(v).len() == v.len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 3