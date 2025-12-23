
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

// Lemma to prove the bounds of max_rcur and min_rcur
proof fn lemma_max_min_bounds(seq: Seq<i32>)
    requires
        seq.len() > 0,
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < #[trigger] seq[i] < i32::MAX / 2,
    ensures
        i32::MIN / 2 <= max_rcur(seq) <= i32::MAX / 2,
        i32::MIN / 2 <= min_rcur(seq) <= i32::MAX / 2,
{
    if seq.len() == 1 {
        assert(i32::MIN / 2 < seq.first() < i32::MAX / 2);
        assert(i32::MIN / 2 <= max_rcur(seq) <= i32::MAX / 2);
        assert(i32::MIN / 2 <= min_rcur(seq) <= i32::MAX / 2);
    } else {
        let last_val = seq.last() as int;
        let rest_max = max_rcur(seq.drop_last());
        let rest_min = min_rcur(seq.drop_last());
        lemma_max_min_bounds(seq.drop_last());

        assert(i32::MIN / 2 < last_val < i32::MAX / 2);
        assert(i32::MIN / 2 <= rest_max <= i32::MAX / 2);
        assert(i32::MIN / 2 <= rest_min <= i32::MAX / 2);

        assert(i32::MIN / 2 <= max(last_val, rest_max) <= i32::MAX / 2);
        assert(i32::MIN / 2 <= min(last_val, rest_min) <= i32::MAX / 2);
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

    // Assertion to ensure that max_val - min_val does not cause underflow/overflow
    assert(max_val >= min_val);
    assert(-((i32::MAX / 2) as int) <= min_rcur(arr@));
    assert(max_rcur(arr@) <= (i32::MAX / 2) as int);

    // Make use of the lemma to assert bounds
    lemma_max_min_bounds(arr@); 
    assert(max_rcur(arr@) - min_rcur(arr@) <= i32::MAX as int);
    assert(max_rcur(arr@) - min_rcur(arr@) >= i32::MIN as int);

    (max_val - min_val) as i32
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False