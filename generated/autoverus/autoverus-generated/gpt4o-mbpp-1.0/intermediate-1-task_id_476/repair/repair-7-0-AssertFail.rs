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

proof fn lemma_bounds(seq: Seq<i32>)
    ensures
        i32::MIN / 2 <= min_rcur(seq) <= i32::MAX / 2,
        i32::MIN / 2 <= max_rcur(seq) <= i32::MAX / 2,
{
    // You can implement an induction proof here on the length of the sequence
    // to prove that min_rcur and max_rcur always stay within the bounds.
}

fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < index ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] >= min_val,
            i32::MIN / 2 <= min_val <= i32::MAX / 2, // Added invariant
            i32::MIN / 2 <= max_val <= i32::MAX / 2, // Added invariant
            true, // Maintain progress
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assertion to check bounds before adding max_val and min_val
    assert(i32::MIN <= max_val as i32 + min_val as i32 && max_val as i32 + min_val as i32 <= i32::MAX); 
    // Corrected assertion to ensure bounds on sum

    proof {
        assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] >= min_val); // Proof of min value
        assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max_val); // Proof of max value
        assert(min_rcur(arr@) == min_val as int);
        assert(max_rcur(arr@) == max_val as int);
    }
    
    max_val + min_val
}

} // verus!

//         assert(min_rcur(arr@) == min_val as int);
//   assertion failed: min_rcur(arr@) == min_val as int

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5
// Safe: False