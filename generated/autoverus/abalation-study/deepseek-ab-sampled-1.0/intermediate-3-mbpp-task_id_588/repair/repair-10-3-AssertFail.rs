
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

/// Helper proof: Bounds on max_rcur
proof fn max_rcur_bounds(seq: Seq<i32>, lower: i32, upper: i32)
    requires
        forall|i: int| 0 <= i < seq.len() as int ==> lower <= seq@[i] <= upper,
    ensures
        lower <= max_rcur(seq) <= upper,
{
    match seq.len() {
        0 => { // Handle empty case if necessary, though spec ensures seq.len() > 0
            assert(false); // Shouldn't happen per function requirements
        },
        len => {
            if len == 1 {
                assert(max_rcur(seq) == seq.first() as int);
                assert(lower <= seq.first() <= upper);
            } else {
                max_rcur_bounds(seq.drop_last(), lower, upper);
                assert(max(seq.last() as int, max_rcur(seq.drop_last())) as int == max_rcur(seq));
                assert(seq.last() <= upper);
                assert(max_rcur(seq.drop_last()) <= upper);
                assert(max_seq_last <= upper);
                assert(max_rcur(seq) <= upper);
                
                assert(seq.last() >= lower);
                assert(max_rcur(seq.drop_last()) >= lower);
                assert(max_rcur(seq) >= lower);
            }
        }
    }
}

/// Helper proof: Bounds on min_rcur
proof fn min_rcur_bounds(seq: Seq<i32>, lower: i32, upper: i32)
    requires
        forall|i: int| 0 <= i < seq.len() as int ==> lower <= seq@[i] <= upper,
    ensures
        lower <= min_rcur(seq) <= upper,
{
    match seq.len() {
        0 => { // Handle empty case if necessary
            assert(false); // Shouldn't happen per function requirements
        },
        len => {
            if len == 1 {
                assert(min_rcur(seq) == seq.first() as int);
                assert(lower <= seq.first() <= upper);
            } else {
                min_rcur_bounds(seq.drop_last(), lower, upper);
                assert(min(seq.last() as int, min_rcur(seq.drop_last())) as int == min_rcur(seq));
                assert(seq.last() <= upper);
                assert(min_rcur(seq.drop_last()) <= upper);
                assert(min_rcur(seq) <= upper);
                
                assert(seq.last() >= lower);
                assert(min_rcur(seq.drop_last()) >= lower);
                assert(min_rcur(seq) >= lower);
            }
        }
    }
}

/// Helper proof: Difference does not cause overflow
proof fn max_min_diff_bounded(seq: Seq<i32>, lower: i32, upper: i32)
    requires
        forall|i: int| 0 <= i < seq.len() as int ==> lower <= seq@[i] <= upper,
    ensures
        (max_rcur(seq) as i64) - (min_rcur(seq) as i64) <= (i32::MAX as i64),
{
    max_rcur_bounds(seq, lower, upper);
    min_rcur_bounds(seq, lower, upper);
    
    let max_val = max_rcur(seq);
    let min_val = min_rcur(seq);
    
    assert(max_val as i64 <= upper as i64);
    assert(min_val as i64 >= lower as i64);
    
    let max_diff = upper as i64 - lower as i64;
    assert(max_diff <= i32::MAX as i64);
    
    assert((max_val - min_val as i32) as i64 <= max_diff);
    assert((max_val - min_val as i32) as i64 <= i32::MAX as i64);
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
    
    // Prove bounds on max and min before assertion
    proof {
        max_rcur_bounds(arr@, i32::MIN / 2, i32::MAX / 2);
        min_rcur_bounds(arr@, i32::MIN / 2, i32::MAX / 2);
        max_min_diff_bounded(arr@, i32::MIN / 2, i32::MAX / 2);
    }
    
    // Assert the difference does not cause overflow
    assert((max_val as i64) - (min_val as i64) <= i32::MAX as i64);

    max_val - min_val
}
}


//     assert((max_val as i64) - (min_val as i64) <= i32::MAX as i64);
//   assertion failed: (max_val as i64) - (min_val as i64) <= i32::MAX as i64

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True