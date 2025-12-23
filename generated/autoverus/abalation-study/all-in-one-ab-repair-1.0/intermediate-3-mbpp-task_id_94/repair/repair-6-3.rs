
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
        let mut min_second_index = 0; // Assume the first element is the minimum
        let mut index = 1; // Start from the second element
        while index < arr.len()
            invariant
                1 <= index <= arr.len(), // Ensure index starts from 1 to arr.len()
                0 <= min_second_index < arr.len(), // Ensure min_second_index is within bounds
                forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1], // Keep track of the minimum
                arr.len() > 0, // Array length is positive
                forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2, // Ensure each sub-array has at least 2 elements
        {
            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }
            index += 1;
        }

        // Postcondition proof block
        proof {
            assert(arr.len() > 0); // Ensure array length is positive
            assert(min_second_index < arr.len()); // Ensure min_second_index is within bounds
            assert(forall(|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1])); // Reinforce invariant
            assert(exists|i: int| i == min_second_index &&
                (forall|j: int| 0 <= j < arr.len() ==> arr[min_second_index][1] <= arr[j][1]));
        }

        arr[min_second_index][0] // Return the first element of the sub-array having the minimum second element
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpezxnhkvv`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False