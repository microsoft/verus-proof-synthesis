use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut j: usize = 0;
    
    while j < v.len()
        invariant
            0 <= j <= v.len(),
            exists |q:int| j <= q < v.len() && v[q] % 2 == 1,
    {
        if v[j] % 2 == 1 {
            return j;
        }
        j = j + 1;
    }

    // The ensures clause guarantees an odd number will be found,
    // so this return statement should be unreachable.
    j
}
}
// Score: (2, 0)
// Safe: False