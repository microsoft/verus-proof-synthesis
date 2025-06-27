use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len() && v[( odd_index ) as int] % 2 == 1,
{
    let mut j: usize = 0;
    while (j < v.len())
        invariant
            j <= v.len(),
            exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,
            forall |k:int| 0 <= k < j ==> v[k] % 2 != 1,
    {
        if (v[j] % 2 == 1) {
            return j;
        }
        j = j + 1;
    }
    j
}
}

// Score: (2, 0)
// Safe: False