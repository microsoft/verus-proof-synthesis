
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
            0 <= i < j < arr.len() ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    while (index < arr.len() - 1)
        invariant
            0 <= index < arr.len(),
            forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]),
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
        decreases arr.len() - index,
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
        proof {
            // Establish the base case for index = 0
            if index == 1 {
                assert(arr[0] + 1 == arr[1]);
                continue;
            }
            // Use induction to extend the condition
            let prev_index = index - 1;
            assert(arr[prev_index] + 1 == arr[prev_index + 1]);
            proof {
                // The induction step: if the condition holds for all pairs up to prev_index,
                // and the next pair also holds, then it holds for all pairs up to index.
                for i in (..prev_index) {
                    for j in (i+1..=index) {
                        assert(arr[i] + 1 == arr[j]);
                    }
                }
            }
        }
    }
    true
}

} // verus!


//             assert(forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False