
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

proof fn lemma_max_rcur_bounds(seq: Seq<i32>)
    requires
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < seq[i] < i32::MAX / 2,
    ensures
        i32::MIN / 2 < max_rcur(seq) < i32::MAX / 2,
{
    if seq.len() > 0 {
        ensures_at_least_union(seq.last() as int, max_rcur(seq.drop_last()), i32::MIN / 2, i32::MAX / 2);
        lemma_max_rcur_bounds(seq.drop_last());
    }
}

proof fn lemma_min_rcur_bounds(seq: Seq<i32>)
    requires
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < seq[i] < i32::MAX / 2,
    ensures
        i32::MIN / 2 < min_rcur(seq) < i32::MAX / 2,
{
    if seq.len() > 0 {
        ensures_at_least_union(seq.last() as int, min_rcur(seq.drop_last()), i32::MIN / 2, i32::MAX / 2);
        lemma_min_rcur_bounds(seq.drop_last());
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
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2,
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }

    // Ensure no underflow or overflow
    assert(max_val as int - min_val as int >= i32::MIN as int);
    assert(max_val as int - min_val as int <= i32::MAX as int);

    (max_val - min_val)
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False