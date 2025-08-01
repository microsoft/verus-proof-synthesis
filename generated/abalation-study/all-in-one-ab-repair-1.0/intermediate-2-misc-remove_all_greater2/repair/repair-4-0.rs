
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            // Elements are distinct
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        ensures
            // All elements in result are less than or equal to e and were in the original array
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            // All elements in the original array that are less than or equal to e are in the result
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        
        while i < v.len()
            invariant
                // The length of the original vector remains constant
                v.len() == vlen, 
                // Length of result does not exceed the current index i
                result.len() <= i,
                // All elements in result fulfill the postcondition
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
                // Validity of processed elements
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
                // Loop advancement bound
                i <= v.len(),
                // Elements are still distinct
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        {
            if v[i] <= e {
                result.push(v[i]);
            }
            i = i + 1;
        }
        
        result
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpeyequ5l7`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False