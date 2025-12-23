
use vstd::prelude::*;
fn main() {}

verus! {
    fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
        requires
            arr.len() > 0, // The array must have at least one row.
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2, // Every row must have at least two elements.
        ensures
            exists|i: int|
                0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] &&
                (forall|j: int| 0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    {
        let mut min_second_index = 0;
        let mut index = 0;

        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                0 <= min_second_index < arr.len(),
                forall|i: int| 0 <= i < index ==> arr[min_second_index][1] <= arr[i][1],
                arr.len() > 0,
                forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        {
            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }
            index += 1;
            proof {
                // Ensure that the invariants are maintained at each iteration.
                assert(0 <= index <= arr.len()); // Index invariant
                assert(0 <= min_second_index < arr.len()); // Min second index invariant
                assert(forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2); // Array length invariant
                if index - 1 >= 0 && index - 1 < arr.len() && arr[index - 1][1] < arr[min_second_index][1] {
                    assert(forall|i: int| 0 <= i < index - 1 ==> arr[min_second_index][1] <= arr[i][1]);
                }
            }
        }
        arr[min_second_index][0]
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpxxj6zw7l`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True