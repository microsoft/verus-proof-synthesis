
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
                result.len() as int <= i as int,
                forall|k: int| 0 <= k < i as int && v[k as usize] <= e ==> result@.contains(v[k as usize]),
                forall|k: int| 0 <= k < result.len() as int ==> result[k as usize] <= e && v@.contains(result[k as usize]),
                i as int <= v.len() as int,
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1 as usize] != v[k2 as usize], // Repeated invariant
        {
            if v[i] <= e {
                result.push(v[i]);
            }
            i = i + 1;
        }
        result
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp1inkif5m`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False