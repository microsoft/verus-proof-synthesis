
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // All elements are unique
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Result only contains values <= e
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // All values <= e in `v` are in result
    {
        let mut i: usize = 0; // Iteration variable
        let vlen = v.len(); // Original length of vector `v`
        let mut result: Vec<i32> = vec![]; // Result vector
        while i < v.len()
            invariant
                v.len() == vlen, // Length of `v` is invariant
                result.len() <= i, // Result length is always <= `i`
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), // Elements added to `result` if `v[k] <= e`
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Result contains only elements <= e
                i <= v.len(), // `i` is always within bounds
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Elements in `v` are unique
        {
            if v[i] <= e {
                result.push(v[i]); // Adds element to result if <= e
            }
            i += 1; // Increment `i`
        }
        result // Return result vector
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp07qi6_96`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False