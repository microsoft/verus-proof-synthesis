use vstd::prelude::*;

fn main() {
    // Write a function in Rust to get a deep clone of a list.

    assert_eq!(list_deep_clone(&vec![5, 2, 3, 3]), [5, 2, 3, 3]);
    assert_eq!(list_deep_clone(&vec![3, 4, 7, 2, 6, 9]), [3, 4, 7, 2, 6, 9]);
    assert_eq!(
        list_deep_clone(&vec![6, 8, 3, 5, 7, 3, 5, 87]),
        [6, 8, 3, 5, 7, 3, 5, 87]
    );
}

verus! {

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied_array = Vec::with_capacity(arr.len());
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            copied_array.len() == index,
            forall|i: int| (0 <= i < index) ==> arr[i] == copied_array[i],
    {
        copied_array.push(arr[index]);
        index += 1;
    }
    copied_array
}

} // verus!
