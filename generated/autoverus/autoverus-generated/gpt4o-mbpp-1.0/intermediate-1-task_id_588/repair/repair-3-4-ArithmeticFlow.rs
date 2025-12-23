
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
        0 <= i <= j <= seq.len(),
    ensures
        max_rcur(seq.subrange(0, i)) <= max_rcur(seq.subrange(0, j)),
    decreases j
{
    if i < j {
        lemma_monotonic_max(seq, i, j - 1);
        assert(max_rcur(seq.subrange(0, i)) <= max(max_rcur(seq.subrange(0, j - 1)), seq[(j - 1) as int] as int));
    }
}

proof fn lemma_monotonic_min(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= seq.len(),
    ensures
        min_rcur(seq.subrange(0, i)) >= min_rcur(seq.subrange(0, j)),
    decreases j
{
    if i < j {
        lemma_monotonic_min(seq, i, j - 1);
        assert(min_rcur(seq.subrange(0, i)) >= min(min_rcur(seq.subrange(0, j - 1)), seq[(j - 1) as int] as int));
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < arr[i] < i32::MAX / 2,
    ensures
        diff == (max_rcur(arr@) - min_rcur(arr@)) as i32, // Assert the correctness of diff
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < arr[i] < i32::MAX / 2,
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < arr[k] < i32::MAX / 2, // Array elements are not modified in the loop
            index <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, index as int)),
            min_val == min_rcur(arr@.subrange(0, index as int)),
            arr.len() == arr.len(),
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }

    assert(max_val as int >= min_val as int) by {
        lemma_monotonic_max(arr@, 0, arr.len() as int);
        lemma_monotonic_min(arr@, 0, arr.len() as int);
    };

    let difference = max_val - min_val;

    assert(difference as int == max_rcur(arr@) - min_rcur(arr@)) by {
        assert(max_rcur(arr@) - min_rcur(arr@) == max_val as int - min_val as int);
    };

    difference
}

} // verus!




//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False