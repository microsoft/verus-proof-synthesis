
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

proof fn lemma_monotonic_max(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < seq.len(),
    ensures
        max_rcur(seq.subrange(0, i + 1)) <= max_rcur(seq.subrange(0, j + 1)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_max(seq, i, j - 1);
    }
}

proof fn lemma_monotonic_min(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < seq.len(),
    ensures
        min_rcur(seq.subrange(0, i + 1)) >= min_rcur(seq.subrange(0, j + 1)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_min(seq, i, j - 1);
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
    // Ensure that max_val >= min_val before performing the subtraction
    assert(min_val <= max_val) by {
        lemma_monotonic_max(arr@, 0, arr.len() - 1);
        lemma_monotonic_min(arr@, 0, arr.len() - 1);
    };
    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 6
// Safe: True