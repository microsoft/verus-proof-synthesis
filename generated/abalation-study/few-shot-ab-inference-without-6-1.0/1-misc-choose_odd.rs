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
    while (j < v.len())
        invariant
            j <= v.len(),
            exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,
            // Loop invariant ensures if we have not found an odd number yet, there is still at least one left in the array
            forall |i:int| 0 <= i < j ==> v[i] % 2 == 0,
    {
        if (v[j] % 2 == 1) {
            return j;
        }
        j = j + 1;
    }
    j // This line is actually unreachable due to the ensures clause and should not be hit, but necessary for compilation
}
}
// Score: (2, 0)
// Safe: True