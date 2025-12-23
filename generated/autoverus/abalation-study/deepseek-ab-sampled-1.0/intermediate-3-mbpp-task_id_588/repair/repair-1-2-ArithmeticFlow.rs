
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;
fn main() {}
verus! {

spec fn max_rcur(seq:Seq<i32>) -> int
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
            forall|i: int| 0 <= i < arr.len() ==> max_val >= arr[i], // arr is never modified in the loop
            forall|i: int| 0 <= i < arr.len() ==> min_val <= arr[i], // arr is never modified in the loop
            index <= arr.len(),
            max_val >= arr[index - 1],
            min_val <= arr[index - 1],
            min_val <= max_val,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    //Assertion added to prevent overflow
    assert(max_val - min_val <= i32::MAX);

    max_val - min_val
}

}


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 4
// Safe: True