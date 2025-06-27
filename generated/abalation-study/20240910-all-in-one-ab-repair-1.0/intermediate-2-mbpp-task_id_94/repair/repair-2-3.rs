
use vstd::prelude::*;
fn main() {}

verus! {
    fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
        requires
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        ensures
            exists|i: int|
                0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && 
                (forall|j: int| 0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    {
        let n = arr.len();
        let mut min_second_index = 0;
        let mut index = 0;
        while index < n
            invariant
                0 <= index <= n,
                0 <= min_second_index < n,
                arr.len() > 0,
                forall|i: int| 0 <= i < index ==> arr[min_second_index][1] <= arr[i][1],
                forall|i: int| 0 <= i < n ==> #[trigger] arr[i].len() >= 2,
        {
            if arr[index][1] < arr[min_second_index][1] {
                min_second_index = index;
            }
            index += 1;
        }
        arr[min_second_index][0]
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpd7nhblo6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False