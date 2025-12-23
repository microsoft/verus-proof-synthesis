
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

proof fn lemma_monotonic_max_min(seq: Seq<i32>)
    requires 
        seq.len() > 0,
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < seq[i] < i32::MAX / 2,
    ensures
        max_rcur(seq) - min_rcur(seq) < i32::MAX as int,
        max_rcur(seq) - min_rcur(seq) >= i32::MIN as int,
{
    // By the given conditions, all elements are within bounds
    // Therefore, the difference between max and min will also be within bounds
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
            1 <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            max_val == max_rcur(arr@.subrange(0, index as int)),
            min_val <= max_val,
            min_val == min_rcur(arr@.subrange(0, index as int)),
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2, // This invariant ensures that the property holds for all elements in the array.
            arr.len() == arr.len(),
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assertion to ensure no overflow/underflow
    assert(max_val as int - min_val as int < i32::MAX as int) by {
        lemma_monotonic_max_min(arr@);
    };
    assert(max_val as int - min_val as int >= i32::MIN as int) by {
        lemma_monotonic_max_min(arr@);
    };

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False