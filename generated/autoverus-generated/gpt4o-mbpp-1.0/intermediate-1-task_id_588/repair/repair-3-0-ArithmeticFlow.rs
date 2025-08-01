
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

proof fn lemma_bounds_max_min(seq: Seq<i32>)
    requires
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < # [trigger] seq[i] < i32::MAX / 2,
    ensures
        i32::MIN / 2 <= min_rcur(seq) <= max_rcur(seq) <= i32::MAX / 2,
{
    if seq.len() == 1 {
        // Base case: single element sequence
    } else if seq.len() > 1 {
        let last = seq.last();
        let rest = seq.drop_last();
        lemma_bounds_max_min(rest);
        assert(i32::MIN / 2 <= min_rcur(rest) <= max_rcur(rest) <= i32::MAX / 2);
        assert(i32::MIN / 2 <= last < i32::MAX / 2);
        if last as int < min_rcur(rest) {
            assert(min(last as int, min_rcur(rest)) == last as int);
        } else {
            assert(min(last as int, min_rcur(rest)) == min_rcur(rest));
        }
        if last as int > max_rcur(rest){
            assert(max(last as int, max_rcur(rest)) == last as int);
        } else {
            assert(max(last as int, max_rcur(rest)) == max_rcur(rest));
        }
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
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assertion to check bounds of max_val - min_val before computing the result
    assert(max_val - min_val <= i32::MAX as int && max_val - min_val >= i32::MIN as int) by {
        lemma_bounds_max_min(arr@);
    };

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False