
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

proof fn lemma_monotonic_max_rcur(seq: Seq<i32>, i: int, j:int)
    requires
        i <= j,
        0 <= i < seq.len(),
        0 <= j < seq.len(),
    ensures
        max_rcur(seq.take(j + 1)) >= max_rcur(seq.take(i + 1)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_max_rcur(seq, i, j - 1);
    }
}

proof fn lemma_monotonic_min_rcur(seq: Seq<i32>, i: int, j:int)
    requires
        i <= j,
        0 <= i < seq.len(),
        0 <= j < seq.len(),
    ensures
        min_rcur(seq.take(j + 1)) <= min_rcur(seq.take(i + 1)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_min_rcur(seq, i, j - 1);
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
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] >= min_val,
            i32::MIN / 2 <= min_val, // Fixed by AI
            max_val <= i32::MAX / 2, // Fixed by AI
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    assert(min_val >= i32::MIN / 2) by {
        lemma_monotonic_min_rcur(arr@, 0, arr.len() - 1);
    }

    assert(max_val <= i32::MAX / 2) by {
        lemma_monotonic_max_rcur(arr@, 0, arr.len() - 1);
    }

    assert(max_val - min_val >= i32::MIN / 2) by {
        lemma_monotonic_max_rcur(arr@, 0, arr.len() - 1);
        lemma_monotonic_min_rcur(arr@, 0, arr.len() - 1);
    }

    max_val - min_val
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 4