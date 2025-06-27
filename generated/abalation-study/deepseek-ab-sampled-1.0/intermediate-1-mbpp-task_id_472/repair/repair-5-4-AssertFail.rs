

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
    let mut index = 0;
    while index < arr.len() - 1
        invariant
            index <= arr.len(),
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> (arr[i] + 1 == arr[i + 1]),
    {
        if arr[index] + 1 != arr[index + 1] {
            return false;
        }
        index += 1;
        proof {
            assert(arr[index - 1] + 1 == arr[( index ) as int]);
            assert(forall|i: int| 0 <= i < index ==> (arr[i] + 1 == arr[i + 1]));
        }
    }
    proof {
        assert(forall|i: int| 0 <= i < index ==> (arr[i] + 1 == arr[i + 1]));
        assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j]));
    }
    true
}

}


//         assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]); // Added by AI
//   assertion failed: forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False