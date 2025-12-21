use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check if each element of second sequence is smaller than its corresponding element in the first sequence.

    assert!(!is_smaller(&vec![1, 2, 3], &vec![2, 3, 4]));
    assert!(is_smaller(&vec![4, 5, 6], &vec![3, 4, 5]));
    assert!(is_smaller(&vec![11, 12, 13], &vec![10, 11, 12]));
}

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            forall|k: int| 0 <= k < index ==> arr1[k] > arr2[k],
    {
        if arr1[index] <= arr2[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
