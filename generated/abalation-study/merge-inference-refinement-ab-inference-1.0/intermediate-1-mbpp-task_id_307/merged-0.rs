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
            arr@.len() == copied_array@.len(),
            copied_array.len() == index,
            forall|i: int| 0 <= i < index ==> arr[i] == copied_array[i],
            index <= arr.len(),
    {
        copied_array.push(arr[index]);
        index += 1;
    }
    copied_array
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1