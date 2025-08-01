use vstd::prelude::*;

fn main() {}

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
            copied_array.len() == index,
            forall|i: int| 0 <= i < index ==> copied_array[i] == arr[i],
            0 <= index <= arr.len(),
            arr.len() == copied_array.capacity(),
    {
        copied_array.push(arr[index]);
        index += 1;
    }
    copied_array
}

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1