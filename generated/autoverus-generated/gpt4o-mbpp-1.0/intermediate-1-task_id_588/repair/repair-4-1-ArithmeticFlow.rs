
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

proof fn lemma_monotonic_max(seq: Seq<i32>, index: int) 
    requires
        0 <= index <= seq.len(),
    ensures
        max_rcur(seq.subrange(0, index)) <= max_rcur(seq),
    decreases seq.len()
{
    // Proof by induction
    if index < seq.len() {
        lemma_monotonic_max(seq, index + 1);
    }
}

proof fn lemma_monotonic_min(seq: Seq<i32>, index: int) 
    requires
        0 <= index <= seq.len(),
    ensures
        min_rcur(seq) <= min_rcur(seq.subrange(0, index)),
    decreases seq.len()
{
    // Proof by induction
    if index < seq.len() {
        lemma_monotonic_min(seq, index + 1);
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
            1 <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < # [trigger] arr[k] < i32::MAX / 2, // Array elements are not modified in the loop
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

    // Assertion to ensure no overflow or underflow before calculating the difference
    assert(max_val as int - min_val as int <= i32::MAX as int - i32::MIN as int) by {
        lemma_monotonic_max(arr@, arr.len() as int);
        lemma_monotonic_min(arr@, arr.len() as int);
    };

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 8
// Safe: False