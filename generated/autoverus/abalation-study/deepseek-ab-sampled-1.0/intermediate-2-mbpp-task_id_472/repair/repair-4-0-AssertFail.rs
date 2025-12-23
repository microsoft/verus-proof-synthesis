
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
            0 <= index,
            index <= arr.len(),
            arr.len() > 0,
            forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]),
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
        proof {
            let old_index = index - 1;
            if old_index < 0 {
                // Base case: the invariant holds trivially for index = 0
                continue;
            }
            // Inductive step: if the invariant holds up to old_index and arr[old_index] + 1 == arr[old_index + 1], then it holds up to index
            assert(forall|i: int, j: int| 0 <= i < j <= old_index ==> (arr[i] + 1 == arr[j]));
            assert(arr[old_index] + 1 == arr[old_index + 1]);
            // Show that the invariant holds for the new index
            assert(forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]));
        }
    }
    true
}

} // verus!


//             assert(forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j])

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True