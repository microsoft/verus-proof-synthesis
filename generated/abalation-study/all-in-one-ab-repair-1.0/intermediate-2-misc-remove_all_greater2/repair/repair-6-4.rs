
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_invariant_decreases("i < v.len()")]
    fn remove_all_greater(v: Vec<i32>, e: i32) -> Vec<i32>
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = Vec::new(); // Initialize an empty vector
        while i < v.len()
            invariant
                v.len() == vlen,
                result.len() <= i,
                forall|k: int| 0 <= k < i ==> v@.index(k) != e ==> !result@.contains(v@.index(k)),
                forall|k: int| 0 <= k < result.len() ==> result@.index(k) <= e && v@.contains(result[k]),
                i <= v.len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v@.index(k1) != v@.index(k2),
        {
            if v[i] <= e {
                result.push(v[i]);
            }
            i = i + 1;
        }
        
        proof {
            forall|k: int| 0 <= k < result.len() ==> {
                assert(result.len() <= v.len());
                assert(v@.contains(result@.index(k)));
                assert(result@.index(k) <= e);
            }
            forall|k: int| 0 <= k < v.len() && v@.index(k) <= e ==> {
                assert(result@.contains(v@.index(k)));
            }
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp080bic6z`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False