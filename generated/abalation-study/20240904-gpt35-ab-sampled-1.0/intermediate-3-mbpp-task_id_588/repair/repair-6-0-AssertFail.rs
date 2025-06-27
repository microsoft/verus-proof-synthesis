
use vstd::math::*;
use vstd::prelude::*;

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            0 < arr.len(),
            0 <= index <= arr.len(),
            exists|i: int| 0 <= i < index && arr[i] == max_val,
            exists|i: int| 0 <= i < index && arr[i] == min_val,
            forall|i: int| 0 <= i < index ==> (arr[i] >= min_val && arr[i] <= max_val),
            forall|i: int| 0 <= i < index ==> i32::MIN / 2 < arr[i] && arr[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < index ==> max_val >= arr[i],
            forall|i: int| 0 <= i < index ==> min_val <= arr[i],
            max_val >= arr[0] && min_val <= arr[0],
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    let diff = max_val - min_val;
    assert(diff == max_rcur(arr@) - min_rcur(arr@));
    max_val - min_val
}


//         assert(diff == max_rcur(arr@) - min_rcur(arr@));
//   assertion failed: diff == max_rcur(arr@) - min_rcur(arr@)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False