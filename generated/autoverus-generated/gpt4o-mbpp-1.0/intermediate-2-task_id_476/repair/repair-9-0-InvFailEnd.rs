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

fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            // arr is never changed in the loop:
            forall|i: int| 0 <= i < index ==> max_val >= #[trigger] arr[i],
            // arr is never changed in the loop:
            forall|i: int| 0 <= i < index ==> min_val <= #[trigger] arr[i],
            arr.len() > 0,
            arr.len() == arr.len(),
            // Ensuring min_val within range
            i32::MIN / 2 < min_val < i32::MAX / 2,
            // Ensuring max_val within range
            i32::MIN / 2 < max_val < i32::MAX / 2,
            // Ensures min_rcur and max_rcur restore correct values from start to index
            min_rcur(arr@.subrange(0, index as int)) == min_val as int,
            max_rcur(arr@.subrange(0, index as int)) == max_val as int,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assertion before computing the sum to avoid overflow/underflow
    proof {
        assume(arr.len() > 0); // Ensure the array is non-empty
        assert(max_rcur(arr@.subrange(0, arr.len() as int)) == max_val as int); // Updated the assertion to cover the entire array
        assert(min_rcur(arr@.subrange(0, arr.len() as int)) == min_val as int); // Updated the assertion to cover the entire array
        assert(max_rcur(arr@.subrange(0, index as int)) == max_val as int); // Correct invariant assertion
    }
    
    proof {
        assert(
            i32::MIN <= (max_val as i64 + min_val as i64) && 
            (max_val as i64 + min_val as i64) <= i32::MAX
        );
    }
    
    max_val + min_val
}

} // verus!

//             max_rcur(arr@.subrange(0, index as int)) == max_val as int,
//   None: max_rcur(arr@.subrange(0, index as int)) == max_val as int

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3
// Safe: True