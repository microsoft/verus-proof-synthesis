use vstd::prelude::*;

fn main() {}

verus! {

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    let mut index = 0;

    while index < arr.len() - 1
        invariant
            index <= arr.len() - 1,
            forall |i:int| 0 <= i < index ==> arr[i] <= arr[i + 1],
            // arr doesn't change length during the loop
            arr.len() > 0,
    {
        if arr[index] > arr[index + 1] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1