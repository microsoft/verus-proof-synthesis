
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

proof fn lemma_monotonic_max(seq1: Seq<i32>, seq2: Seq<i32>)
    requires
        seq1.len() <= seq2.len(),
    ensures
        max_rcur(seq1) <= max_rcur(seq2),
    decreases (seq2.len() - seq1.len()), // Assume this measure is non-negative
{
    if seq1.len() == seq2.len() {
        // Base case: If seq1 has the same length as seq2, they are the same.
    } else {
        // Recursive case: Drop the last element of seq2 and call the lemma on the smaller sequence.
        lemma_monotonic_max(seq1, seq2.drop_last());
    }
}

proof fn lemma_monotonic_min(seq1: Seq<i32>, seq2: Seq<i32>)
    requires
        seq1.len() <= seq2.len(),
    ensures
        min_rcur(seq1) <= min_rcur(seq2),
    decreases (seq2.len() - seq1.len()), // Assume this measure is non-negative
{
    if seq1.len() == seq2.len() {
        // Base case: If seq1 has the same length as seq2, they are the same.
    } else {
        // Recursive case: Drop the last element of seq2 and call the lemma on the smaller sequence.
        lemma_monotonic_min(seq1, seq2.drop_last());
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
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
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2, // Added invariant to cover every element of arr, assuming arr is not modified in the loop
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Adding assertion before the critical arithmetic operation
    assert(max_val >= min_val);

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 6
// Safe: True