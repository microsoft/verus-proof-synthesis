use vstd::prelude::*;
fn main() {}

verus!{
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            0 <= i1 <= i2 < v.len(),
            exists|i:int| i1 <= i <= i2 && k == v[i],
            forall|a:int, b:int| 0 <= a <= b < i1 ==> v[a] <= v[b],
            forall|a:int, b:int| i2 <= a <= b < v.len() ==> v[a] <= v[b],
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    i1
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 3