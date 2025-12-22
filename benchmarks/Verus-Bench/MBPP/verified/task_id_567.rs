use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether a specified list is sorted or not.

    assert!(is_sorted(&vec![1, 2, 4, 6, 8, 10, 12, 14, 16, 17]));
    assert!(!is_sorted(&vec![1, 2, 4, 6, 8, 10, 12, 14, 20, 17]));
    assert!(!is_sorted(&vec![1, 2, 4, 6, 8, 10, 15, 14, 20]));
}

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
            0 <= index <= arr.len() - 1,
            forall|k: int, l: int| 0 <= k < l <= index ==> arr[k] <= arr[l],
    {
        if arr[index] > arr[index + 1] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
