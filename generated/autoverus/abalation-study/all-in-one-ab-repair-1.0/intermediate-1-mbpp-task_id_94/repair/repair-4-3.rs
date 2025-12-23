
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
    fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
        requires
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        ensures
            exists|i: int|
                0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                    0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    {
        // Invariant: arr.len() > 0 is already part of the requires
        let mut min_second_index = 0;
        let mut index = 0;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                0 <= min_second_index < arr.len(),
                // Ensure we check min_second_index when index is 0
                0 <= index ==> arr.len() > 0,
                // Ensure the current min_second_index holds the minimum second value within checked range
                forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1],
                // Ensure the size and structure of arr is upheld
                forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        {
            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }
            index += 1;
        }
        arr[min_second_index][0]
    }

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprrb2ameh`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True