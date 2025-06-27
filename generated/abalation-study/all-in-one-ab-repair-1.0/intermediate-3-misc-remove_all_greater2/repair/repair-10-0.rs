
use vstd::prelude::*;
fn main() {}

verus! {
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

        while (i < v.len())
            invariant
                v.len() == vlen,
                result.len() <= i,
                forall|k: int| 0 <= k < i ==> (v[k] <= e ==> result@.contains(v[k])),
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
                i <= v.len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        {
            if (v[i] <= e) {
                result.push(v[i]);

                proof {
                    let idx = result.len() as int - 1; // The index of the new element in the result list
                    assert(result@[idx] <= e);
                    assert(v@.contains(result@[idx]));
                    assert(result.len() <= i + 1);
                }
            }
            i += 1;
        }

        proof {
            // Ensure all postconditions are satisfied before returning the result
            assert(forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]));
            assert(forall|k: int| 0 <= k < v.len() ==> (v[k] <= e ==> result@.contains(v[k])));
        }

        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_rrlh_cs`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False