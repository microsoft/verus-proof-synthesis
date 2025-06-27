
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
                result.len() <= i as int,
                forall|k: int| 0 <= k < i as int ==> (v[k] <= e ==> result@.contains(v[k])),
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
                i as int <= v.len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        {
            if v[i] <= e {
                result.push(v[i]);

                proof {
                    let idx = result.len() as int - 1; // The index of the new element in the result list
                    assert(result@[idx] <= e);
                    assert(v@.contains(result@[idx]));
                    assert(result.len() as int <= i as int + 1);
                }
            }
            i += 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7ec0xi_m`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False