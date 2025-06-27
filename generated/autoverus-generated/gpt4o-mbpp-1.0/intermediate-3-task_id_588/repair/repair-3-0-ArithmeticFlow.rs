
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

proof fn lemma_monotonic_max(seq: Seq<i32>, len1: int, len2: int)
    requires
        len1 <= len2,
        0 <= len1 <= seq.len(),
        0 <= len2 <= seq.len(),
    ensures
        max_rcur(seq.subrange(0, len1)) <= max_rcur(seq.subrange(0, len2)),
{
    if len1 < len2 {
        lemma_monotonic_max(seq, len1, len2 - 1);
    }
}

proof fn lemma_monotonic_min(seq: Seq<i32>, len1: int, len2: int)
    requires
        len1 <= len2,
        0 <= len1 <= seq.len(),
        0 <= len2 <= seq.len(),
    ensures
        min_rcur(seq.subrange(0, len1)) >= min_rcur(seq.subrange(0, len2)),
{
    if len1 < len2 {
        lemma_monotonic_min(seq, len1, len2 - 1);
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
            1 <= index <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, index as int)),
            min_val == min_rcur(arr@.subrange(0, index as int)),
            arr.len() == arr.len(),
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < # [trigger] arr[k] < i32::MAX / 2, // Added invariant to cover every element of arr, assuming arr is not modified in the loop
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    
    // Assertion to ensure max_val - min_val does not overflow
    assert(min_val <= max_val);
    assert((max_val - min_val) <= ((i32::MAX / 2) - (i32::MIN / 2))); // Ensures no overflow or underflow based on given bounds

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True