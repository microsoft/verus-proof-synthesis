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
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> min_val <= # [trigger] arr[i] <= max_val,
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
            max_val == max_rcur(arr@.subrange(0, (index) as int)),
            min_val == min_rcur(arr@.subrange(0, (index) as int)),
            arr.len() > 0,
            // The array `arr` is never modified in the loop, hence the invariant covers every element in the array.
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            arr.len() == arr.len(),
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
        proof {
            assert(min_val == min_rcur(arr@.subrange(0, index as int))); // Added by AI
        }
    }
    max_val - min_val
}

} // verus!

//             min_val == min_rcur(arr@.subrange(0, (index) as int)),
//   None: min_val == min_rcur(arr@.subrange(0, (index) as int))

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3
// Safe: True