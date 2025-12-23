use vstd::prelude::*;
fn main() {}
verus! {

fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            0 <= i1 <= i2 < v.len(),
            exists|i: int| i1 <= i <= i2 && k == v[i],
            forall|m: int| 0 <= m < i1 ==> v[m] < k,
            forall|m: int| i2 < m < v.len() ==> v[m] >= k,
            forall|x: int| 0 <= x < i1 ==> v[x] < k,
            forall|x: int| i2 < x < v.len() ==> v[x] >= k,
            forall|a: int, b: int| 0 <= a <= b < i1 ==> v[a] <= k && k <= v[b],
            forall|a: int, b: int| i2 <= a <= b < v.len() ==> v[a] <= k && k <= v[b],
            i1 <= i2 < v.len(),
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

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 6