
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
            1 <= index,
            arr.len() > 0,
            forall|i: int| 0 <= i < index ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            index <= arr.len(),
            max_val >= min_val, // Strengthened invariant to include this condition
            max_val - min_val <= i32::MAX / 2, // Ensuring difference doesn't overflow
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    assert(max_val >= min_val); // This now follows directly from the invariant
    assert(i32::MAX / 2 - (i32::MIN / 2) >= max_val - min_val); // Directly assert bounds based on specified limits
    max_val - min_val
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2