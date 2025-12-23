
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        while i < v.len()
            invariant
                v.len() == vlen,
                result.len() <= i,
                forall|k: int| 0 <= k < i ==> v[k] <= e ==> result@.contains(v[k]),
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
                i <= v.len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        {
            if v[i] <= e {
                result.push(v[i]);
                proof {
                    assert(result@.last() == Some(v[i]));
                    assert(result@[result.len() as int - 1] <= e && v@.contains(result@[result.len() as int - 1]));
                    assert(result.len() <= i + 1);
                }
            }
            i = i + 1;
        }
        proof {
            // Ensure that the postconditions are met:
            // 1. Each element in the result is less than or equal to e and is contained in the original vector.
            // 2. Each element in the original vector which is less than or equal to e is included in the result.
            assert(forall|k: int| 0 <= k < result@.len() ==> result@[k] <= e && v@.contains(result@[k]));
            assert(forall|k: int| 0 <= k < vlen && v@[k] <= e ==> result@.contains(v@[k]));
        }
        result
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpe2ujdo5i`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False