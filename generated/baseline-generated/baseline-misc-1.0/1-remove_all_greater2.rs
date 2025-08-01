use vstd::prelude::*;
fn main() {}
verus!{
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{  
    let mut i: usize = 0;
    let mut result: Vec<i32> = vec![];
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            v@.len() == v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i as int && v[k] <= e ==> result@.contains(v[k]),
    {  
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
    }  
    result
}
}
// Score: (1, 1)
// Safe: False