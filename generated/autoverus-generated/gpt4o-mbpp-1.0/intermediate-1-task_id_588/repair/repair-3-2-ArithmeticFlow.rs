
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

// Lemma to establish bounds on max_rcur and min_rcur
proof fn lemma_bounds_max_min(seq: Seq<i32>)
    ensures
        max_rcur(seq) <= i32::MAX / 2,
        min_rcur(seq) >= i32::MIN / 2,
{
    if seq.len() <= 1 {
        assert(seq.first() <= i32::MAX / 2);
        assert(seq.first() >= i32::MIN / 2);
    } else {
        lemma_bounds_max_min(seq.drop_last());
        assert(max(seq.last() as int, max_rcur(seq.drop_last())) <= i32::MAX / 2);
        assert(min(seq.last() as int, min_rcur(seq.drop_last())) >= i32::MIN / 2);
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == (max_rcur(arr@) - min_rcur(arr@)) as i32,
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

    assert(max_val as int <= i32::MAX / 2 && min_val as int >= i32::MIN / 2) by {
        lemma_bounds_max_min(arr@.subrange(0, index as int));
    };

    // Adding assertion to ensure no overflow/underflow
    assert(max_val as int - min_val as int <= i32::MAX);
    assert(max_val as int - min_val as int >= i32::MIN);

    (max_val - min_val) as i32
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False