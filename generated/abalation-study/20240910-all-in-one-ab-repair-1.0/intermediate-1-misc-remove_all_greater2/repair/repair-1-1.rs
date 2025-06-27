
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
            forall|k: int| 0 <= k < i ==> v[k] <= e || !result.contains(&v[k]),
            forall|k: int| 0 <= k < result.len() ==> result@.contains(result[k]) && result[k] <= e,
            i <= v.len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], 
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
    }
    result
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmps013n2hc`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False