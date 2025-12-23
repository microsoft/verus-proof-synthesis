
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
    let mut result: Vec<i32> = vec ! [];
    while (i < v.len())
        invariant
            forall|j: int| 0 <= j < i ==> v[j] > e || result@.contains(v[j]),
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall|k:int| 0 <= k < v.len() ==> v[k] != v[k], // Ensuring the invariant covers every element since v is never modified in the loop
            i <= v.len(),
            vlen == v.len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
            v.len() == vlen,
            result.len() <= vlen,
    {
        if (v[i] <= e) {
            result.push(v[i]);
        }
        i = i + 1;
    }
    result
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1