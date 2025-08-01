use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    while index < arr.len() - 1
        invariant
            0 <= index < arr.len(),
            0 <= index <= arr.len() - 1,
            arr.len() == arr.len(), // Loop invariant for the length of the array
            0 <= #[trigger] arr[index as int] + 1 < i32::MAX, // copying the invariant here
    {
        proof {
            if index > 0 {
                assert(arr[index - 1] + 1 == arr[( index ) as int]); // Added by AI, for assertion fail
            }
        }
        if arr[index] + 1 != arr[index + 1] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!


//         assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False