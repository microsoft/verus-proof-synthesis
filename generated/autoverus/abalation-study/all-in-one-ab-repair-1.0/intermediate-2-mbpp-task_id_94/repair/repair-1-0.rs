
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
                    0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    {
        let n = arr.len();
        let mut min_second_index = 0;
        for i in 1..n 
            invariant
                0 <= i <= n,
                0 <= min_second_index < n,
                forall|k: int| 0 <= k < i ==> arr[min_second_index][1] <= #[trigger] arr[k][1],
                arr.len() > 0,
                forall|j: int| 0 <= j < n ==> #[trigger] arr[j].len() >= 2,
        {
            if arr[i][1] < arr[min_second_index][1] {
                min_second_index = i;
            }
        }
        arr[min_second_index][0]
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphgolxtg8`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False