
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Elements must be distinct
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Result contains elements <= e from v
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // All elements <= e in v are in result
    {
        let mut i: usize = 0; // Initialize index
        let vlen = v.len();
        let mut result: Vec<i32> = vec![]; 

        while i < v.len()
            invariant
                v.len() == vlen, // Length of v is maintained
                result.len() <= i, // Result size condition
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), // Preservation from initial
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Elements in result condition
                i <= v.len(), // Valid index
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Elements distinct condition repeated
        {
            if v[i] <= e { // Check condition
                result.push(v[i]); // Add to result if condition met
            }
            i = i + 1; // Increment index
        }
        result // Return result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpms6501px`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False