
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> Vec<i32>
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // ensuring all elements are unique
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        while i < v.len()
            invariant
                v.len() == vlen, // Vector length doesn't change
                result.len() <= i, // Result length is always less than or equal to i
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), // Ensuring result has elements <= e
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Ensuring validity of result elements
                i <= v.len(), // Ensuring i does not exceed v length
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Repeated invariant to ensure vector integrity
        {
            if v[i] <= e {
                result.push(v[i]);
            }
            i = i + 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpyn9874wi`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False