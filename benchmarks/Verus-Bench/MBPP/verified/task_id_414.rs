use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether any value in a sequence exists in a sequence or not.

    assert!(!any_value_exists(&vec![1, 2, 3, 4, 5], &vec![6, 7, 8, 9]));
    assert!(!any_value_exists(&vec![1, 2, 3], &vec![4, 5, 6]));
    assert!(any_value_exists(&vec![1, 4, 5], &vec![1, 4, 5]));
}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
{
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|k: int| 0 <= k < index ==> !arr2@.contains(#[trigger] arr1[k]),
    {
        if (contains(arr2, arr1[index])) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
