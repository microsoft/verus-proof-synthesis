
use vstd::prelude::*;
fn main() {}
verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
            &&& arr[idx as int] % 2 != 0
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            arr.len() == input_len,
            arr@.len() == arr.len(),
            arr@.len() == input_len,
            forall|i: int| 0 <= i < index ==> arr[i] % 2 == 0,
            // The following has been changed to cover every element in the array
            forall|k: int| 0 <= k < arr.len() ==> (if k < index { arr[k] % 2 == 0 } else { true }),
            // Comment: The array `arr` is never changed in this loop
            index <= arr.len(),
            input_len == arr.len(),
    {
        if (arr[index] % 2 != 0) {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!
