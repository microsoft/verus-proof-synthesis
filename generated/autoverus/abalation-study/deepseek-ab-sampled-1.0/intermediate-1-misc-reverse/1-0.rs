

use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall |i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;

    while (n < length / 2)
        invariant
            n <= length / 2,
            v.len() == length,
            v.len() == old(v).len(),
            forall |i: int| 0 <= i < (n as int) ==> 
                v[i] == old(v)[length as int - i - 1],
            forall |i: int| (length as int - (n as int )) <= i < length as int ==> 
                v[i] == old(v)[i - (length as int - (n as int ))],
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
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3