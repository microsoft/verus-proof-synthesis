
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

fn main() {}
verus! {

spec fn max_rcur(seq:Seq<i32>) -> int
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

// Helper lemma to prove that the difference between any two elements in the array is within i32 bounds
proof fn bounded_difference(x: i32, y: i32)
    requires
        x > i32::MIN / 2,
        x < i32::MAX / 2,
        y > i32::MIN / 2,
        y < i32::MAX / 2,
    ensures
        (x as i64) - (y as i64) <= i32::MAX as i64,
{
    have h1: i32::MIN / 2 < x < i32::MAX / 2;
    have h2: i32::MIN / 2 < y < i32::MAX / 2;
    assert(x as i64 <= i32::MAX / 2 as i64);
    assert(y as i64 >= i32::MIN / 2 as i64);
    assert(x as i64 - y as i64 <= (i32::MAX / 2 as i64) - (i32::MIN / 2 as i64));
    assert((i32::MAX / 2 as i64) - (i32::MIN / 2 as i64) <= i32::MAX as i64);
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
            forall|i: int| 0 <= i < index ==> max_val >= arr[i],
            forall|i: int| 0 <= i < index ==> min_val <= arr[i],
            index <= arr.len(),
            max_val >= arr[index - 1],
            min_val <= arr[index - 1],
            min_val <= max_val,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    // Use the lemma to prove the difference is within i32 bounds
    bounded_difference(max_val, min_val);
    assert((max_val as i64) - (min_val as i64) <= i32::MAX as i64);

    let diff: i32 = max_val - min_val;
    diff
}

}


//     assert((max_val as i64) - (min_val as i64) <= i32::MAX as i64);
//   assertion failed: (max_val as i64) - (min_val as i64) <= i32::MAX as i64

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False