use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether a list of numbers contains only one distinct element or not.

    assert!(has_only_one_distinct_element(&vec![1, 1, 1]));
    assert!(!has_only_one_distinct_element(&vec![1, 2, 1, 2]));
    assert!(!has_only_one_distinct_element(&vec![1, 2, 3, 4, 5]));
}

verus! {

fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() <= 1 {
        return true;
    }
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> arr[0] == #[trigger] arr[k],
    {
        if arr[0] != arr[index] {
            assert(exists|i: int| 1 <= i < arr@.len() && arr[0] != #[trigger] arr[i]);
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
