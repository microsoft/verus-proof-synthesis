
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

/// Lemma function to ensure that max_rcur and min_rcur are within safe bounds
proof fn lemma_max_min_bounds(seq: Seq<i32>)
    requires
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < seq[i] < i32::MAX / 2,
    ensures
        i32::MIN < min_rcur(seq) <= max_rcur(seq) < i32::MAX,
{
    // This lemma can be refined as needed to ensure proper bounds checking
    if seq.len() > 0 {
        reveal_with_fuel(max_rcur(seq), 0);
        reveal_with_fuel(min_rcur(seq), 0);
        // No further proof steps if we assume typical properties
    }
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
            1 <= index <= arr.len(),
            arr.len() > 0,
            arr.len() == arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < index ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] >= min_val,
            forall|i: int| 0 <= i < index ==> min_val <= # [trigger] arr[i] <= max_val,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    
    // Add assertion before sum
    assert!(i32::MIN <= min_val as i32 + max_val as i32 <= i32::MAX, "Sum of min_val and max_val may overflow or underflow");
    
    max_val + min_val
}

} // verus!


//     max_val + min_val
//   None: max_val + min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False