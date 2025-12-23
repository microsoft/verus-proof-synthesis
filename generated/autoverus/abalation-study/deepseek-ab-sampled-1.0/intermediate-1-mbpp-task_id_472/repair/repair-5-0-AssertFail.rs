
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0; // Start from the first element
    while index < arr.len() - 1 {
        if arr[index] + 1 != arr[index + 1] {
            return false;
        }
        index += 1;
    }
    // Verify that all consecutive elements satisfy the condition
    if arr.len() > 1 {
        proof {
            for_range |i: int| 0 <= i < arr.len() {
                if i >= 1 {
                    assert(arr[i - 1] + 1 == arr[i]);
                }
            }
        }
    }
    true
}

}


//         assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]); // Added by AI
//   assertion failed: forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False