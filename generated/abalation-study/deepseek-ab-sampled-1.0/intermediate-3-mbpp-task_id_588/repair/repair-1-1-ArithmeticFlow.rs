
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

// Lemma to show monotonicity of the difference between max_rcur and min_rcur
proof fn lemma_bounds(seq: Seq<i32>)
    requires
        seq.len() > 0,
        forall |i: int| 0 <= i < seq.len() ==>
            (seq[i] > (i32::MIN / 2) as int) && (seq[i] < (i32::MAX / 2) as int),
    ensures
        (max_rcur(seq) - min_rcur(seq)) > i32::MIN as int &&
        (max_rcur(seq) - min_rcur(seq)) < i32::MAX as int
{
    // Prove the difference is within the valid i32 range
    let max = max_rcur(seq);
    let min = min_rcur(seq);
    assert(max > min);
    assert(max - min > i32::MIN as int);
    assert(max - min < i32::MAX as int);
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall |i: int| 0 <= i < arr.len() ==>
            (arr[i] > (i32::MIN / 2) as int) && (arr[i] < (i32::MAX / 2) as int),
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            forall |i: int| 0 <= i < arr.len() ==> max_val >= arr[i],
            forall |i: int| 0 <= i < arr.len() ==> min_val <= arr[i],
            index <= arr.len(),
            max_val >= arr[index - 1],
            min_val <= arr[index - 1],
            min_val <= max_val,
            forall |i: int| 0 <= i < arr.len() ==>
                (arr[i] > (i32::MIN / 2) as int) && (arr[i] < (i32::MAX / 2) as int),
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }

    // Add assertion about the bound of max_val - min_val
    assert(max_val - min_val > i32::MIN as int);
    assert(max_val - min_val < i32::MAX as int);

    max_val - min_val
}

}.


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False