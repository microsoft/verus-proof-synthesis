
use vstd::math::*;
use vstd::prelude::*;

fn main() {}
verus! {

spec fn max_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==>
            i32::MIN / 2 < #[trigger] arr[i] && arr[i] <= i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            forall|i: int| 0 <= i < index ==> max_val >= arr[i],
            forall|i: int| 0 <= i < index ==> min_val <= arr[i],
            index <= arr.len(),
            max_val >= arr[index - 1],
            min_val <= arr[index - 1],
            min_val <= max_val,
            forall|i: int| 0 <= i < arr.len() ==>
                i32::MIN / 2 < #[trigger] arr[i] && arr[i] <= i32::MAX / 2,
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }
    // Calculate difference safely
    let max_min_diff = (max_val as i64) - (min_val as i64);
    // Ensure difference does not cause overflow
    if max_min_diff > i32::MAX as i64 {
        panic!("Difference exceeds i32::MAX");
    }
    let diff = max_min_diff as i32;

    max_val - min_val // This is acceptable as per the ensures clause
}

}


//     assert((max_val as i64) - (min_val as i64) <= i32::MAX as i64);
//   assertion failed: (max_val as i64) - (min_val as i64) <= i32::MAX as i64

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False