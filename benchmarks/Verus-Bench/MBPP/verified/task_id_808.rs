use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check if the given sequence contain the k or not.

    assert!(contains_k(&vec![10, 4, 5, 6, 8], 6));
    assert!(!contains_k(&vec![1, 2, 3, 4, 5, 6], 7));
    assert!(contains_k(&vec![7, 8, 9, 44, 11, 12], 11));
}

verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|m: int| 0 <= m < index ==> (arr[m] != k),
    {
        if (arr[index] == k) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
