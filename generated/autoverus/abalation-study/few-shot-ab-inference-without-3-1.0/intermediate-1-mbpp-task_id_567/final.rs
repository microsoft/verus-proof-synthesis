
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    let mut index = 0;
    while index < arr.len() - 1
        invariant
            // The loop does not modify the array `arr`, hence the invariant should cover all elements in the array.
            forall|k: int, l: int| 0 <= k < l < arr.len() ==> (arr[k] <= arr[l]),
            index <= arr.len() - 1,
            arr.len() > 0,
            arr.len() == arr.len(),
    {
        if arr[index] > arr[index + 1] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1