use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether the given integer is greater than the elements of the given integer array.

    assert!(!is_greater(&vec![1, 2, 3, 4, 5], 4));
    assert!(is_greater(&vec![2, 3, 4, 5, 6], 8));
    assert!(is_greater(&vec![9, 7, 4, 8, 6, 1], 11));
}

verus! {

fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> number > arr[k],
    {
        if number <= arr[i] {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
