

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
        let n = arr.len(); // Number of sub-arrays.
        
        for i in 0..n
            invariant
                0 <= i <= n,
                exists |min_index: int| 0 <= min_index < n && (forall|k: int| 0 <= k < i ==> arr[min_index][1] <= arr[k][1]),
                arr.len() > 0,
                forall|j: int| 0 <= j < arr.len() ==> #[trigger] arr[j].len() >= 2,
        {
            if arr[idx][1] < arr[min_second_index][1] { // `index` to `idx` (index is protected keyword).
                min_second_index = idx;
            }
            idx += 1;
            proof { assert(arr.len() > 0); }
            arr[min_second_index][0] should be first_of_min_second, { output block } or output = arr[min_second_index][0];
        }
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpoi6enhli`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False