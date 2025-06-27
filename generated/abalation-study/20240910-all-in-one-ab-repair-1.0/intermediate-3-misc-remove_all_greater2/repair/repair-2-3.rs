
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
                forall|k: int| 0 <= k < i ==> (v[k] <= e ==> result@.contains(v[k])),
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
                i <= v.len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Unique elements constraint
        {
            if v[i] <= e {
                result.push(v[i]);
                proof {
                    // Proving that the pushed value conforms to all specified properties
                    let ghost_result = result.clone();
                    assert forall|k: int| 0 <= k < (ghost_result.len() as int) ==> ghost_result[k] <= e && v@.contains(ghost_result[k]) by {
                        assert(ghost_result[len(ghost_result) as int - 1] <= e);
                        assert(v@.contains(ghost_result[len(ghost_result) as int - 1]));
                    };
                }
            }
            i = i + 1;
        }
        result
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_g5dy8ik`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False