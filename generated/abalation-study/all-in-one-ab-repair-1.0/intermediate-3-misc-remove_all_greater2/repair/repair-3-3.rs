
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
        forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Ensuring all elements are unique in v
    ensures
        forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Ensuring all elements of result are <= e and exist in v
        forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // Ensuring all elements in v <= e exist in result
{
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while i < v.len()
        invariant
            v.len() == vlen, // Length of v does not change
            result.len() <= i, // Result length doesn't exceed the current index
            forall|k: int| 0 <= k < i ==> (v[k] <= e ==> result@.contains(v[k])), // All elements processed that are <= e should be in result
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Elements in result should be <= e and exist in v
            i <= v.len(), // Current index doesn't exceed the length of v
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Ensuring all elements are unique in v (repeated invariant)
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
        proof {
            assert(forall|k: int| 0 <= k < i ==> (v[k] <= e ==> result@.contains(v[k])));
        }
    }
    result
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzkisvq4b`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False