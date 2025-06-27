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
            forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],
            forall|j: int| (j >= n as int && j < length as int - n as int) ==> v[j] == old(v)[j],
            forall|k: int| 0 <= k < n ==> v[k] == old(v)[length - 1 - k],
            forall|k: int| 0 <= k < n ==> v[k] == old(v)[length - k - 1],
            forall|k: int| n <= k < length - n ==> v[k] == old(v)[k],
            length == old(v).len(),
            n < length,
            n <= length,
            forall|k: int| 0 <= k < n as int ==> v[k] == old(v)[(length - 1 - k) as int],
            forall|k: int| n as int <= k < (length - n) as int ==> v[k] == old(v)[k as int],
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


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2