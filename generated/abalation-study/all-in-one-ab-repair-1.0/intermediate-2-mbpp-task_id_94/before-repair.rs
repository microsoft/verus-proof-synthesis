
use vstd::prelude::*;
fn main() {}
verus! {

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
            forall|i: int| 0 <= i < index ==> arr[(min_second_index) as int][1] <= arr[i][1],
            forall|j: int|
                0 <= j < index ==> arr[(min_second_index) as int][1] <= # [trigger] arr[j][1],
            forall|j: int| 0 <= j < index ==> arr[(min_second_index) as int][1] <= arr[j][1],
            // Changed to cover the whole array because arr is never modified
            forall|k: int|
                0 <= k < arr.len() ==> arr[(min_second_index) as int][1] <= # [trigger] arr[k][1], // arr is never modified inside the loop
            arr.len() > 0, // repeated from requires
            forall|i: int| 0 <= i < arr.len() ==> # [trigger] arr[i].len() >= 2, // repeated from requires
            arr.len() == arr.len(),   // Length invariant
    {
        if arr[index][1] < arr[min_second_index][1] {
            min_second_index = index;
        }
        index += 1;
    }
    arr[min_second_index][0]
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4