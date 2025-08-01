
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
        let mut index = 1; // Starting from 1 since 0 is already the initial min_second_index
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                0 <= min_second_index < arr.len(),
                forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1],
                arr.len() > 0,
                forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        {
            proof {
                assert(0 <= min_second_index < arr.len()); // Reinforce invariant scope
                assert(forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1]); // Reinforce invariant scope
            }

            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }

            index += 1;
        }

        proof {
            assert(arr.len() > 0); // Ensure array length is positive
            assert(0 <= min_second_index < arr.len()); // Ensure index is within bounds
            assert(forall|i: int| 0 <= i < index ==> arr[min_second_index as int][1] <= arr[i][1]); // Reinforce invariant
        }

        arr[min_second_index][0]
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpext3tc84`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False