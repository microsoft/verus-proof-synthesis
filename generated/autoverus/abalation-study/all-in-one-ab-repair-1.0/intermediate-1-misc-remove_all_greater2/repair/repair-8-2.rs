
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            // Ensures elements in v are unique
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], 
        ensures
            // Ensures all elements in output result are <= e and were originally in v
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), 
            // Ensures all elements of v that are <= e are present in the result
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), 
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        while i < v.len()
            invariant
                v.len() == vlen, //len of v does not change
                result.len() <= i, //len of result is always <= i
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), //all elements in v from 0 to i that are <= e are in result
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), //all elements in result are from v and <= e
                i <= v.len(), //i is always within the range of v
                // elements in v are unique
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprvloy9k3`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False