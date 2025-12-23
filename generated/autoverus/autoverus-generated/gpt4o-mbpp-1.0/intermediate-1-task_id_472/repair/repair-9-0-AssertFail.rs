use vstd::prelude::*;
fn main() {}

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    while (index < arr.len() - 1)
        invariant
            0 <= index < arr.len(),
            0 <= index <= arr.len() - 1,
            arr.len() == arr.len(), // Loop invariant for the length of the array
            forall|k: int| 0 <= k <= index ==> (0 <= #[trigger] arr[k] + 1 < i32::MAX), // ensuring it's true for all elems seen so far
            forall|i: int, j: int| 0 <= i < j <= index && j == i + 1 ==> (arr[i] + 1 == arr[j]), // ensuring consecutive property for elems seen so far
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
        proof {
            assert(forall|k: int| 0 <= k <= index ==> 0 <= #[trigger] arr[k] + 1 < i32::MAX);
        }
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j]));
    }
    true
}

} // verus!

//             assert(forall|k: int| 0 <= k <= index ==> 0 <= #[trigger] arr[k] + 1 < i32::MAX);
//   assertion failed: forall|k: int| 0 <= k <= index ==> 0

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True