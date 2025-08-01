
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
            arr.len() == old(arr.len()), // Ensuring array length stays constant
            min_val <= max_val, // Added to maintain logical consistency about min_val and max_val
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
        proof {
            assert(arr.len() > 0);
            assert(forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < arr[i] < i32::MAX / 2);
            assert(forall|i: int| 0 <= i < index ==> max_val >= arr[i]);
            assert(forall|i: int| 0 <= i < index ==> min_val <= arr[i]);
            assert(min_val <= max_val);
        }
    }
    proof {
        assert(arr.len() == old(arr.len()));
        assert(min_val <= max_val);
        assert(sum == max_rcur(arr@) + min_rcur(arr@)); // This assertion makes no sense here, we should remove this.
    }
    proof {
       let arr_seq = arr@;
       assert(max_rcur(arr_seq) == max_val as int);
       assert(min_rcur(arr_seq) == min_val as int);
    }
    max_val + min_val
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmph3senqn6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True