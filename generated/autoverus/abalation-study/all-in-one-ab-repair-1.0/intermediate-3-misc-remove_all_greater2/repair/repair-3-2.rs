
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // No duplicates in the vector v
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // result only contains elements <= e from original v
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // All elements from v <= e are in the result
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        
        while i < v.len()
            invariant
                v.len() == vlen, // Length of v remains constant
                result.len() <= i, // Length of result is at most i (all processed elements)
                forall|k: int| 0 <= k < i ==> (v[k] <= e ==> result@.contains(v[k])), // All processed elements <= e are in result
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // All elements in result are <= e and existed in v
                i <= v.len(), // i is within bounds of v
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Repeated invariant ensuring uniqueness
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
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmps_eokpe6`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False