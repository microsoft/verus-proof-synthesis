use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the index of the first occurrence of a given number in a sorted array.

    assert_eq!(
        find_first_occurrence(&vec![2, 5, 5, 5, 6, 6, 8, 9, 9, 9], 5),
        Some(1)
    );
    assert_eq!(
        find_first_occurrence(&vec![2, 3, 5, 5, 6, 6, 8, 9, 9, 9], 5),
        Some(2)
    );
    assert_eq!(
        find_first_occurrence(&vec![2, 4, 1, 5, 6, 6, 8, 9, 9, 9], 6),
        Some(4)
    );
    assert_eq!(
        find_first_occurrence(&vec![2, 4, 1, 5, 6, 6, 8, 9, 9, 9], 10),
        None
    );
}

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
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|k: int| 0 <= k < index ==> arr[k] != target,
    {
        if arr[index] == target {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!
