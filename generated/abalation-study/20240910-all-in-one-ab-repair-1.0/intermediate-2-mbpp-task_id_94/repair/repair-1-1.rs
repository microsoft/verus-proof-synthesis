
use vstd::prelude::*;
fn main() {}

verus! {

fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> arr[i][1] <= #[trigger] arr[j][1]),
{
    if arr.len() == 0 {
        return 0; // This should be unreachable due to the `requires` clause but added for completeness
    }

    let mut min_second_index = 0;
    let mut index = 1; // Start from the second element in the array
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= min_second_index < arr.len(),
            // Invariant: for every processed element at index, arr[min_second_index][1] should be <= arr[i][1]
            forall|i: int| 0 <= i < index ==> arr[min_second_index][1] <= #[trigger] arr[i][1],
            arr.len() > 0, // repeated from requires
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2, // repeated from requires
    {
        if arr[index][1] < arr[min_second_index][1] {
            min_second_index = index;
        }
        index += 1;
    }

    arr[min_second_index][0]
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4nuau6bg`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False