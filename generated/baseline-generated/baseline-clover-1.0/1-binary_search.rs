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
            exists|i: int| i1 as int <= i <= i2 as int && k == v[i],
            forall|a: int, b: int| 0 <= a <= b < v.len() ==> v[a] <= v[b],
    {
        let ghost d = i2 - i1;

        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            proof {
                // Prove that the element k exists in the subrange [ix + 1, i2] 
                assert(exists|i: int| ix < i <= i2 as int && k == v[i]);
            }
            i1 = ix + 1;
        } else {
            proof {
                // Prove that the element k exists in the subrange [i1, ix]
                assert(exists|i: int| i1 as int <= i <= ix as int && k == v[i]);
            }
            i2 = ix;
        }
    }
    assert(k == v[i1 as int]); // Prove that k is equal to v[i1] when the loop terminates
    i1
}

} // verus!
// Score: (2, 0)
// Safe: True