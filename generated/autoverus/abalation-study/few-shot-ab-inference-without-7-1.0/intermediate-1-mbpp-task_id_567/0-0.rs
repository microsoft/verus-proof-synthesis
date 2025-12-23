use vstd::prelude::*;

fn main() {}

verus! {

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    let mut index = 0;
    while index < arr.len() - 1
        invariant
            0 <= index < arr.len(),
            forall|i: int, j: int| 0 <= i <= index < j < arr.len() ==> (arr[i] <= arr[j]),
    {
        if arr[index] > arr[index + 1] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3