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
    while (index < arr.len() - 1)
        invariant
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
            arr.len() == arr.len(),
            forall|k: int| 0 <= k <= index ==> (k + 1 < arr.len() ==> (arr[k] + 1 == arr[k + 1])), // Added by AI
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])); // Added by AI
    }
    true
}

} // verus!

// failed this postcondition
//         is_consecutive == (forall|i: int, j: int|
//             0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
// at the end of the function body
// {
//     let mut index = 0;
//     while (index < arr.len() - 1)
//         invariant
// ...
//     true
// }
//   at the end of the function body: {     let mut index = 0;     while (index < arr.len() - 1)         invariant             arr.len() > 0,             forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),             arr.len() == arr.len(),             // Adding invariant to cover every element in the array             forall|k: int| 0 <= k < arr.len() ==> (0 <= #[trigger] arr[k] + 1 < i32::MAX) // Array is never changed in the loop     {         if (arr[index] + 1 != arr[index + 1]) {             return false;         }         index += 1;     }     true }
//   failed this postcondition: is_consecutive == (forall|i: int, j: int|             0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True