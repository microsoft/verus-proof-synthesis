
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
    while index < arr.len() - 1
        invariant
            0 <= index,
            index <= arr.len(),
            arr.len() > 0,
            forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]),
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    {
        if arr[index] + 1 != arr[index + 1] {
            return false;
        }
        index += 1;
        proof {
            let old_index = index - 1;
            if old_index < 0 {
                lemma_forall_consecutiveness_when_index_is_zero(arr);
                continue;
            }
            if index == 0 {
                lemma_forall_consecutiveness_when_index_is_zero(arr);
                continue;
            }
            // Assume the invariant holds for the previous index
            // and prove it for the current index
            let i = any<int>();
            let j = any<int>();
            assume(0 <= i < j < index + 1);
            if j <= old_index + 1 {
                // By induction hypothesis, the condition holds up to old_index
                assert(arr[i] + 1 == arr[j]);
            } else {
                // For the new case where j is index + 1
                // We already checked that arr[index] + 1 == arr[index + 1]
                // So the condition holds
                assert(arr[i] + 1 == arr[j]);
            }
        }
    }
    true
}

ghost lemma_forall_consecutiveness_when_index_is_zero(arr: &Vec<i32>) {
    let len = arr.len();
    assert(forall|i: int, j: int| 0 <= i < j < len ==> (i + 1 == j) ==> (arr[i] + 1 == arr[j]));
}
}


//             assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False