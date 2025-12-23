
use vstd::prelude::*;
fn main() {}

verus! {

// Ensure no duplicate elements in the vector
spec fn unique_elements(v: Seq<i32>) -> bool {
    forall |k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
}

pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires
        unique_elements(v@),
    ensures
        forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall|k: int| 0 <= k < v.len() && v@.index(k) <= e ==> result@.contains(v@.index(k)),
{
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = Vec::new();
    
    while i < v.len()
        invariant
            v.len() == vlen,
            result.len() <= i,
            forall|k: int| 0 <= k < i ==> v@.index(k) <= e ==> result@.contains(v@.index(k)),
            forall|k: int| 0 <= k < result.len() ==> result@.index(k) <= e && v@.contains(result@.index(k)),
            i <= v.len(),
            unique_elements(v@), // Simplified invariant
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
    }
    
    result
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpk1jcm5li`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False