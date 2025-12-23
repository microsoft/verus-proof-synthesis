
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

proof fn lemma_max_monotonic(seq1: Seq<i32>, seq2: Seq<i32>)
    requires
        seq1.len() <= seq2.len(),
        forall|i: int| 0 <= i < seq1.len() ==> #[trigger] seq1[i] == seq2[i],
    ensures
        max_rcur(seq1) <= max_rcur(seq2)
{
    // Proving the lemma of monotonicity for max_rcur
    if seq1.len() == seq2.len() {
        // When both sequences have the same length
        assert(seq1 == seq2);
    } else {
        let len1 = seq1.len();
        let len2 = seq2.len();
        let rest_seq2 = seq2.subrange(0, len2 - 1);
        lemma_max_monotonic(seq1, rest_seq2);
    }
}

proof fn lemma_min_monotonic(seq1: Seq<i32>, seq2: Seq<i32>)
    requires
        seq1.len() <= seq2.len(),
        forall|i: int| 0 <= i < seq1.len() ==> #[trigger] seq1[i] == seq2[i],
    ensures
        min_rcur(seq1) >= min_rcur(seq2)
{
    // Proving the lemma of monotonicity for min_rcur
    if seq1.len() == seq2.len() {
        // When both sequences have the same length
        assert(seq1 == seq2);
    } else {
        let len1 = seq1.len();
        let len2 = seq2.len();
        let rest_seq2 = seq2.subrange(0, len2 - 1);
        lemma_min_monotonic(seq1, rest_seq2);
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
            1 <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2, // Array elements are not modified in the loop
            index <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, (index) as int)),
            min_val == min_rcur(arr@.subrange(0, (index) as int)),
            arr.len() == arr.len(),
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assertion to ensure no underflow/overflow occurs
    assert(max_val - min_val >= 0) by {
        // Ensuring that the difference is non-negative given that min_val <= max_val
        assert(( lemma_max_monotonic(arr@.subrange(0, ( index ) as int), arr@) ) as bool);
        assert(lemma_min_monotonic(arr@.subrange(0, index), arr@));
    };

    (max_val - min_val) as i32
}

} // verus!




//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False