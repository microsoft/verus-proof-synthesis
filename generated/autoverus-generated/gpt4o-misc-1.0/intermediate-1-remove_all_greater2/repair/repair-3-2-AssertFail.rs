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
    while (i < v.len())
        invariant
            forall|j: int| 0 <= j < i ==> v[j] > e || result@.contains(v[j]),
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            i <= v.len(),
            vlen == v.len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
            result.len() <= v.len(),
    {
        if (v[i] <= e) {
            result.push(v[i]);
        }
        i += 1;
    }
    proof {
        assert(result.len() <= v.len());
    }
    result
}

} // verus!

//             assert(result.len() <= v.len());
//   assertion failed: result.len() <= v.len()

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False