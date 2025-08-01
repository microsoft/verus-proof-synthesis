
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

// This function removes all elements from the vector `v` that are greater than the integer `e`.
// The resulting vector is guaranteed to:
// 1. Contain only elements that are less than or equal to `e`.
// 2. Contain all elements from `v` that are less than or equal to `e`.
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
        forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Ensures elements in 'v' are unique.
    ensures
        forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Result vector contains elements <= e from 'v'.
        forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // All elements <= e in 'v' are in the result.
{
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];

    while i < v.len()
        invariant
            v.len() == vlen, // The length of 'v' does not change.
            result.len() <= i, // The length of 'result' is at most 'i'.
            forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), // All processed elements <= e are in 'result'.
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // 'result' elements are valid.
            i <= v.len(), // 'i' is within the bounds of 'v'.
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Elements in 'v' remain unique.
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
    }
    result
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphkc1j9dz`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False