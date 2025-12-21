use vstd::prelude::*;

fn main() {
    // Write a function in Rust that takes in an array and element and checks whether all items in the array are equal to the given element.

    assert!(!all_elements_equals(&vec![1, 3, 5, 7, 9, 2, 4, 6, 8], 3));
    assert!(all_elements_equals(&vec![1, 1, 1, 1, 1, 1, 1], 1));
    assert!(!all_elements_equals(&vec![5, 6, 7, 4, 8], 6));
}

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> (arr[k] == element),
    {
        if arr[index] != element {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
