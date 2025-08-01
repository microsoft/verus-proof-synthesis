
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier(loop_isolation = true)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // elements are unique
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // all elements in output are <= e and from v
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // all elements from v that are <= e are in result
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        while (i < v.len())
            invariant
                v.len() == vlen, // len of v does not change
                result.len() <= i, // len of result is always <= i
                forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), // all elements in v from 0 to i that are <= e are in result
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // all elements in result are from v and <= e
                i <= v.len(), // i is always within the range of v
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // elements in v are unique
        {
            if (v[i] <= e) {
                result.push(v[i]);
            }
            i = i + 1;
        }
        result
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpcc1udva5`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True