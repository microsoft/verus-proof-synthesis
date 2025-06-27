
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_sorted_and_unique(v: Seq<i32>) -> bool {
        forall |k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] <= v[k2]
    }

    fn remove_all_greater(v: &Vec<i32>, e: i32) -> Vec<i32>
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.spec_len() ==> v.spec_index(k1) != v.spec_index(k2),
        ensures
            forall|k: int| 0 <= k < result.spec_len() ==> result.spec_index(k) <= e && #[trigger] v.spec_contains(result.spec_index(k)),
            forall|k: int| 0 <= k < v.spec_len() && v.spec_index(k) <= e ==> result.spec_contains(v.spec_index(k)),
    {
        let mut result = Vec::new();
        let mut i = 0;
        while i < v.len()
            invariant
                v.spec_len() == old(v).spec_len(),
                result.spec_len() <= i,
                forall|k: int| 0 <= k < i ==> (v.spec_index(k) <= e ==> result.spec_contains(v.spec_index(k))),
                forall|k: int| 0 <= k < result.spec_len() ==> result.spec_index(k) <= e && #[trigger] v.spec_contains(result.spec_index(k)),
                i <= v.spec_len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.spec_len() ==> v.spec_index(k1) != v.spec_index(k2),
        {
            if v[i] <= e {
                result.push(v[i]);

                proof {
                    let idx = result.spec_len() as int - 1; // Index of the newly added element
                    assert(result.spec_index(idx) <= e);
                    assert(v.spec_contains(result.spec_index(idx)));
                    assert(result.spec_len() <= i + 1);
                }
            }
            i += 1;
        }

        proof {
            // Ensure all postconditions are satisfied before returning the result
            assert(forall|k: int| 0 <= k < result.spec_len() ==> result.spec_index(k) <= e && #[trigger] v.spec_contains(result.spec_index(k)));
            assert(forall|k: int| 0 <= k < v.spec_len() && v.spec_index(k) <= e ==> result.spec_contains(v.spec_index(k)));
        }

        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8wlhut8s`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False