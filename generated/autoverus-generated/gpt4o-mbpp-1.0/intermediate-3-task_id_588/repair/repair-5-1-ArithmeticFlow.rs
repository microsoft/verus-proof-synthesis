
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

proof fn lemma_max_monotonic(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < seq.len(),
    ensures
        max_rcur(seq.subrange(0, i + 1)) <= max_rcur(seq.subrange(0, j + 1)),
    decreases seq.len() - j
{
    if i < j {
        lemma_max_monotonic(seq, i, j - 1);
    }
}

proof fn lemma_min_monotonic(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < seq.len(),
    ensures
        min_rcur(seq.subrange(0, j + 1)) <= min_rcur(seq.subrange(0, i + 1)),
    decreases seq.len() - j
{
    if i < j {
        lemma_min_monotonic(seq, i, j - 1);
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
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < # [trigger] arr[k] < i32::MAX / 2,
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }

    assert(max_val >= min_val); // Assertion to check bounds before performing subtraction

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 8
// Safe: False