use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the maximum difference between any two elements in a given array.

    assert_eq!(max_difference(&vec![2, 1, 5, 3]), 4);
    assert_eq!(max_difference(&vec![9, 3, 2, 5, 1]), 8);
    assert_eq!(max_difference(&vec![3, 2, 1]), 2);
}

verus! {

fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];

    let mut index = 1;
    while index < arr.len()
        invariant
            i32::MIN / 2 < min_val < i32::MAX / 2,
            i32::MIN / 2 < max_val < i32::MAX / 2,
            min_val <= max_val,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            forall|k: int| 0 <= k < index ==> min_val <= arr[k] && arr[k] <= max_val,
    {
        if (arr[index] < min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    max_val - min_val
}

} // verus!
