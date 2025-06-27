
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
            forall|i: int| 0 <= i < index ==> max_val >= #[trigger] arr[i], // Invariant for max_val
            forall|i: int| 0 <= i < index ==> min_val <= #[trigger] arr[i], // Invariant for min_val
            arr@.len() > 0,
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }
    proof {
        // Adding the final proof to match ensure clause
        assert(max_rcur(arr@) == max_val as int);
        assert(min_rcur(arr@) == min_val as int);
    }
    max_val + min_val
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnvf0qrw9`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 4
// Safe: False