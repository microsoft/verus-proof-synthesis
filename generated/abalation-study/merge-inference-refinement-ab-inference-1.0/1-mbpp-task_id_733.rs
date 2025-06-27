use vstd::prelude::*;

fn main() {}

verus! {

fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        if let Some(idx) = index {
            &&& 0 <= idx < arr.len()
            &&& forall|k: int| 0 <= k < idx ==> arr[k] != target
            &&& arr[idx as int] == target
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
{
    let mut idx = 0;
    while idx < arr.len()
        invariant 
            idx <= arr.len(),
            forall|k: int| 0 <= k < idx ==> arr[k] != target,
    {
        if arr[idx] == target {
            return Some(idx);
        }
        idx += 1;
    }
    None
}

} // verus!
// Score: (2, 0)
// Safe: False