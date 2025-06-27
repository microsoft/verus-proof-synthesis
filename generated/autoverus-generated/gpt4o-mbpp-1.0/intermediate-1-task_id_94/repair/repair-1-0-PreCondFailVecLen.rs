
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> # [trigger] arr[i].len() >= 2,
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == # [trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= # [trigger] arr[j][1])),
{
    let mut min_second_index = 0;
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= min_second_index < arr.len(),
            forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1],
            forall|j: int|
                0 <= j < index ==> arr[min_second_index as int][1] <= # [trigger] arr[j][1],
            forall|j: int| 0 <= j < index ==> arr[min_second_index as int][1] <= arr[j][1],
            // Changed to cover the whole array because arr is never modified
            forall|k: int|
                0 <= k < arr.len() ==> arr[min_second_index as int][1] <= # [trigger] arr[k][1], // arr is never modified inside the loop
            arr.len() > 0, // repeated from requires
            forall|i: int| 0 <= i < arr.len() ==> # [trigger] arr[i].len() >= 2, // repeated from requires
            arr.len() == arr.len(),   // Length invariant
            0 <= index < arr.len(), // Index invariant for arr[index]
            0 <= min_second_index < arr.len(), // Index invariant for arr[min_second_index]
            0 <= 1 < arr[( index ) as int].len(), // Index invariant for arr[index][1]
            0 <= 1 < arr[( min_second_index ) as int].len(), // Index invariant for arr[min_second_index][1]

    {
        if arr[index][1] < arr[min_second_index][1] {
            min_second_index = index;
        }
        index += 1;
    }
    arr[min_second_index][0]
}

} // verus!




//         if arr[index][1] < arr[min_second_index][1] {
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: arr[index][1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True