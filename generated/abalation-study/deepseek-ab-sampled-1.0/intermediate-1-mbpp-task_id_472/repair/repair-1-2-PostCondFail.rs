
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
    let len = arr.len();
    if len == 0 {
        return false;
    }
    let mut index = 0;
    while index < len - 1 {
        // Invariant: All elements up to index satisfy the consecutive condition
        invariant
            0 <= index <= len - 1,
            forall|i: int| 0 <= i < index ==> arr[i] + 1 == arr[i + 1],
        {
            if arr[index] + 1 != arr[index + 1] {
                return false;
            }
            index += 1;
        }
    }
    true
}

}


// failed this postcondition
//         is_consecutive == (forall|i: int, j: int|
//             0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
// at the end of the function body
// {
//     let mut index = 0;
//     while (index < arr.len() - 1) {
//         // Loop invariant: index <= arr.len()
// ...
//     true
// }
//   at the end of the function body: {     let mut index = 0;     while (index < arr.len() - 1) {         // Loop invariant: index <= arr.len()         // A loop invariant for this while loop is:         // - index <= arr.len()         // - forall|i: int| 0 <= i < index ==> arr[i] + 1 == arr[i+1]         // The array arr is not modified in the loop via x.set(), as the loop only performs         // read operations on arr         if (arr[index] + 1 != arr[index + 1]) {             return false;         }         index += 1;     }     true }
//   failed this postcondition: is_consecutive == (forall|i: int, j: int|             0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False