
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
        let n = arr.len();
        let mut min_second_index = 0;
        let mut index = 0;

        proof {
            assert(arr.len() > 0);
            // Assertions to ensure the invariants are correctly set up at the start of the loop
            assert(0 <= min_second_index < arr.len());
            assert(forall(|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1]));
        }

        while index < n
            invariant
                0 <= index <= n,
                0 <= min_second_index < n,
                forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1],
                n == arr.len(),
                forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        {
            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }
            index += 1;
        }

        proof {
            // Ensure array length is positive
            assert(arr.len() > 0);
            // Ensure the final min_second_index is within bounds
            assert(min_second_index < arr.len());
            // Reinforce the invariant at the end of the loop
            assert(forall(|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1]));
            // Postcondition meta-proof to ensure the result meets the specification
            assert(exists|i: int| 0 <= i < arr.len() && arr[min_second_index][1] <= arr[i][1]);
        }

        arr[min_second_index][0]
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphnrc6j3l`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False