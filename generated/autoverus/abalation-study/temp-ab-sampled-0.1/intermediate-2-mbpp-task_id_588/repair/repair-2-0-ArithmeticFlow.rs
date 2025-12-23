
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
        forall|i: int| 0 <= i < seq1.len() ==> seq1[i] == seq2[i],
    ensures
        max_rcur(seq1) <= max_rcur(seq2),
    decreases seq2.len()
{
    if seq1.len() < seq2.len() {
        lemma_monotonic_max(seq1, seq2.drop_last());
    }
}

proof fn lemma_monotonic_min(seq1: Seq<i32>, seq2: Seq<i32>)
    requires
        seq1.len() <= seq2.len(),
        forall|i: int| 0 <= i < seq1.len() ==> seq1[i] == seq2[i],
    ensures
        min_rcur(seq1) >= min_rcur(seq2),
    decreases seq2.len()
{
    if seq1.len() < seq2.len() {
        lemma_monotonic_min(seq1, seq2.drop_last());
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
            forall|i: int| 0 <= i < index ==> max_val >= arr[i],
            forall|i: int| 0 <= i < index ==> min_val <= arr[i],
            max_val == max_rcur(arr@.subrange(0, index as int)),
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

    // Assertion to prevent arithmetic underflow/overflow
    assert(max_val as int - min_val as int <= i32::MAX as int - i32::MIN as int) by {
        lemma_monotonic_max(arr@.subrange(0, index as int), arr@);
        lemma_monotonic_min(arr@.subrange(0, index as int), arr@);
    };

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 6
// Safe: True