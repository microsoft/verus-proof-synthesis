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
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length as int - i - 1],
            forall|i: int| length as int - n <= i < length as int ==> v[i] == old(v)[length as int - i - 1],
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
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3