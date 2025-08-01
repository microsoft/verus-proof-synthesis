
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= # [trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    while (index < arr.len() - 1)
        invariant
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> (0 <= # [trigger] arr[i] + 1 < i32::MAX), // Explained: the array arr is never modified in this loop, thus we generalize the invariant to cover all elements.
            index < arr.len(),
            forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]), // Corrected by AI
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j]));
    }
    true
}

} // verus!


//             forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]), // Added by AI
//   None: forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j])

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True