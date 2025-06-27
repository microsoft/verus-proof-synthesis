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
            exists|m: int| 0 <= m < v.len() && k == v[m] && i1 <= m <= i2,
            forall|x: int, y: int| 0 <= x < i1 && i2 <= y < v.len() ==> v[x as int] < k <= v[y as int],
    {
        let ghost d = i2 - i1;
        
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


// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2