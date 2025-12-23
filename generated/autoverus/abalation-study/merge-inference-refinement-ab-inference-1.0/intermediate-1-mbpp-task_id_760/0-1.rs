use vstd::prelude::*;

fn main() {}

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
            0 < arr.len(),
            index <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> arr.len() == old(arr).len(),
            forall|i: int| 1 <= i < index ==> arr[0] == arr[i], // array is unchanged in the loop
    {
        if arr[0] != arr[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1