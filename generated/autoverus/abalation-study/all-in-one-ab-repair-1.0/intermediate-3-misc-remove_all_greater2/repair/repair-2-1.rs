
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
        forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // All elements are unique
    ensures
        forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // All elements in the result are <= e and were in the original vector
        forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // All elements in the original vector that were <= e are in the result
{
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];
    while i < v.len()
        invariant
            v.len() == vlen,
            result.len() <= i,
            forall|k: int| 0 <= k < i ==> (v[k] > e ==> !result@.contains(v[k])) && (v[k] <= e ==> result@.contains(v[k])),
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // Ensure result items are <= e and were in v
            i <= v.len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // All elements in v are unique
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i += 1;
    }
    result
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpj_y_ki30`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False