
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> Vec<i32>
        requires
            // All elements in the vector must be unique
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        ensures
            // Resulting vector contains only elements <= e and these elements exist in the original vector
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            // All elements <= e in the original vector are part of the resulting vector
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];

        while i < v.len()
            invariant
                v.len() == vlen, // Length of the vector remains unchanged
                result.len() <= i, // Result length is not greater than index 'i'
                // All elements from the input vector that are <= 'e' and come before 'i' are included in 'result'
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
                // All elements in 'result' are <= 'e' and present in original vector 'v'
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
                i <= v.len(), // Index 'i' is bounded by the length of the vector
                // Retaining the requirement of all unique element pairs within the vector
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        {
            proof {
                assert(i < v.len());
                assert(result.len() <= i);
                assert(forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]));
                assert(forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]));
                assert(i <= v.len());
            }

            if v[i] <= e {
                result.push(v[i]);
            }
            i = i + 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp36pgku_a`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False