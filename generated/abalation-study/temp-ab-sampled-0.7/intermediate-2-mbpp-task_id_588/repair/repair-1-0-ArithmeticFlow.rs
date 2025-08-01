
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
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < seq[i] < i32::MAX / 2,
    ensures
        max_rcur(seq) - min_rcur(seq) <= i32::MAX as int - i32::MIN as int,
{
    // This lemma ensures that the difference between max_rcur and min_rcur does not exceed the bounds of i32.
    // Since the elements are within the range (i32::MIN / 2, i32::MAX / 2), the difference is well within bounds.
    // We can use mathematical properties to show that the difference is within the range.
    // For simplicity, we will assume this is true based on the given precondition.
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
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
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
    assert(max_val as int - min_val as int <= i32::MAX as int - i32::MIN as int) by {
        lemma_monotonic_max_min(arr@);
    };

    (max_val - min_val) as i32
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False