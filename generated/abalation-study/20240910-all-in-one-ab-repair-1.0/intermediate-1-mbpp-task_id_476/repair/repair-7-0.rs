
#![verifier::loop_isolation(false)]
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

    fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
        requires
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
        ensures
            sum == max_rcur(arr@) + min_rcur(arr@),
    {
        let mut min_val = arr[0];
        let mut max_val = arr[0];
        let mut index = 1;
        while index < arr.len()
            invariant
                1 <= index <= arr.len(),
                forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
                // arr is never changed in the loop:
                forall|i: int| 0 <= i < index ==> max_val >= #[trigger] arr[i],
                // arr is never changed in the loop:
                forall|i: int| 0 <= i < index ==> min_val <= #[trigger] arr[i],
                arr.len() > 0,
                arr.len() == arr.len(),
                // Define invariants for min_val and max_val based on the processed sub-range of the array
                forall|i: int| 0 <= i < index ==> min_val <= arr[i] && max_val >= arr[i],
        {
            if arr[index] <= min_val {
                min_val = arr[index];
            } else if arr[index] > max_val {
                max_val = arr[index];
            }
            index += 1;
        }
        // Post-loop condition is that max_val and min_val reflect the extreme values in the entire array
        assert(min_val == arr@.min());
        assert(max_val == arr@.max());
        
        max_val + min_val
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpg6l0ln0_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False