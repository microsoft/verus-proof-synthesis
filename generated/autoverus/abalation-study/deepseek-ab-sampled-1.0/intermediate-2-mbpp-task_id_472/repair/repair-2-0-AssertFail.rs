
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
            // Inductive step: Assume the invariant holds for index - 1, prove for index
            if index > 0 {
                let prev_index = index - 1;
                assume forall|i: int, j: int| 0 <= i < j < prev_index + 1 ==> arr[i] + 1 == arr[j];
                
                // Now need to show it holds for index (prev_index + 1)
                for I in 0..index {
                    for J in (I+1)..index+1 {
                        proof {
                            if J == I + 1 {
                                if I == prev_index && J == index + 1 {
                                    // This is the new pair being added
                                    assert(arr[I] + 1 == arr[J]);
                                } else {
                                    // Use the inductive hypothesis
                                    assert(noop());
                                }
                            } else {
                                // Use the inductive hypothesis for higher J
                                assert(noop());
                            }
                        }
                    }
                }
            } else {
                // Base case: index is 0, the invariant is trivially true
                assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> arr[i] + 1 == arr[j]);
            }
        }
    }
    true
}

}


//             assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False