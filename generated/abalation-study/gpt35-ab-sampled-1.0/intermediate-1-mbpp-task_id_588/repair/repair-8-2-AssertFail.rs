
use vstd::math::*;
use vstd::prelude::*;

verus! {

// ... (other function and proof definitions remain the same)

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2, // Fixed by AI
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] >= min_val,
            i32::MIN / 2 <= min_val, // Added by AI, for assertion fail
            i32::MIN / 2 <= max_val, // Added by AI, for assertion fail
            max_val <= i32::MAX / 2, // Fixed by AI
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    lemma_monotonic_min_rcur(arr@, 0, arr.len() - 1); // Added by AI, for assertion fail
    lemma_monotonic_max_rcur(arr@, 0, arr.len() - 1); // Added by AI, for assertion fail

    max_val - min_val
}

} // verus!


//     assert(min_val >= i32::MIN / 2) by {
//   assertion failed: min_val >= i32::MIN / 2

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False