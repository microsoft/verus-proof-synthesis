
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;
fn main() {}
verus! {

// Your spec definitions for max_rcur and min_rcur remain unchanged

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index,
            arr.len() > 0,
            forall|i: int| 0 <= i < index ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            index <= arr.len(),
            max_val - min_val <= i32::MAX / 2, // This is a safety invariant not an under/overflow proof
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assert max_val and min_val are within bounds, this is more of a reiteration.
    assert(max_val <= i32::MAX / 2 && min_val >= i32::MIN / 2); // Direct bound assertion
    assert(max_val - min_val <= i32::MAX / 2); // Reflects ensured bounds, but not necessary due to environmental constraint

    max_val - min_val
}

}


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True