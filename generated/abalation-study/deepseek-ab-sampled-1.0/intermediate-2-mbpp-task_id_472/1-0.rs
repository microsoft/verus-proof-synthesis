

use vstd::prelude::*;

fn main() {}

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
    invariant
        0 < arr.len(),
        index <= arr.len(),
        // For all k where 0 <= k < index, arr[k] + 1 == arr[k + 1]
        forall |k: int| 0 <= k < index as int ==> arr[k] + 1 == arr[k + 1],
        // For all k where index <= k < arr.len() - 1, arr[k] + 1 == arr[k + 1]
        forall |k: int| index as int <= k < arr.len() - 1 ==> arr[k] + 1 == arr[k + 1],
{
    let mut index = 0;
    while (index < arr.len() - 1)
        invariant
            0 <= index <= arr.len(),
            // Elements before index have been checked and are consecutive
            forall |k: int| 0 <= k < index as int ==> arr[k] + 1 == arr[k + 1],
            // Remaining elements are yet to be checked
            forall |k: int| index as int <= k < arr.len() - 1 ==> arr[k] + 1 == arr[k + 1],
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1