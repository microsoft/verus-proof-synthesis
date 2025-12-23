
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> Vec<i32>
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
                let ghost_result = result@.push(v[i] as int); // Added by AI
                proof {
                    assert(ghost_result.len() == result.len() as int + 1); // Added by AI: Update ghost state reasoning
                    assert(forall|k: int| 0 <= k < result.len() ==> (result@.index(k) <= e && v@.contains(result@.index(k)))); // Added by AI: Update reasoning of maintained invariants
                }
                result.push(v[i]);
            }
            i = i + 1;
        }
        proof {
            assert(forall|k: int| 0 <= k < result.len() ==> (result@.index(k) <= e && v@.contains(result@.index(k)))); // Added by AI: Ensuring post condition
            assert(forall|k: int| 0 <= k < v.len() && v.index(k) <= e ==> result@.contains(v.index(k))); // Added by AI: Ensuring post condition
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpy6x7_7dd`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False