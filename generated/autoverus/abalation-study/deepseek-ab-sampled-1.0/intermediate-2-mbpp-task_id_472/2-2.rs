

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
{

    let mut index = 0;

    while (index < arr.len() - 1)
    invariant
        // Ensure that index is within the bounds of the array
        0 <= index < arr.len(),
        // Ensure that the length of the array is at least 1, as required
        arr.len() > 0,
        // Ensure that all previously checked elements satisfy the consecutive condition
        forall |i: int| 0 <= i < index ==> (arr[i] + 1 == arr[i + 1]),
    {

        // Check if the current element and the next element are consecutive
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }

        // Move to the next element
        index += 1;
    }

    // If all elements are consecutive, return true
    true

}
} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1