
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_invariant(maintains(all))] // Ensures all invariants are maintained in the loop
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // No duplicates
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // All result elements are <= e and exist in v
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // All elements in v that are <= e are in the result
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        
        while (i < v.len())
            invariant
                v.len() == vlen, // v has not changed
                result.len() <= i, // result length is guaranteed to be <= i
                forall|k: int| 0 <= k < i ==> v[k] <= e ==> result@.contains(v@)[k], // All elements in result are in v and ≤ e 
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // All elements in result are ≤ e and are present in v
                i <= v.len(), // Ensure i does not surpass the length of v
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Maintain the invariant that all elements in v are unique
        {
            if (v[i] <= e) {
                result.push(v[i]);
            }
            i += 1;
        }
        result
    }
} // verus! block


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpvstgifhe`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False