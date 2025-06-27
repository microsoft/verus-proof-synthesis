
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
        let mut min_second_index = 0;
        let mut index = 0;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                0 <= min_second_index < arr.len(),
                forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1],
                arr.len() > 0,
                forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        {
            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }
            index += 1;
        }

        // Postcondition proof: ensuring our result satisfies the ensures clause
        proof {
            assert(arr.len() > 0); // Ensure array length is positive
            assert(min_second_index < arr.len()); // Ensure min_second_index is within bounds
            assert(forall(|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2)); // Array lengths

            // Proof that the found index is optimal
            assert(exists|i: int| 0 <= i < arr.len() && arr[min_second_index][1] <= arr[i][1]);
            assert(exists|i: int| 0 <= i < arr.len() && arr[min_second_index][1] <= arr[i][1] &&
                (forall|j: int| 0 <= j < arr.len() ==> arr[i][1] <= arr[j][1]));
        }

        arr[min_second_index][0]
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmps6_nnzjy`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True