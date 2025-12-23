
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
            0 <= i < j < arr.len() ==> (arr[i] + 1 == arr[j]) ),
{
    let mut index = 0;
    while index < arr.len() - 1 
        invariant
            0 <= index <= arr.len() - 1,
            arr.len() > 0,
            forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]),
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    {
        if arr[index] + 1 != arr[index + 1] {
            return false;
        }
        proof {
            let old_index = index;
            // After checking index and index+1, the condition up to index+1 holds
            assert(forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> arr[i] + 1 == arr[j]);
        }
        index += 1;
    }
    true
}
}


//             assert(forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False