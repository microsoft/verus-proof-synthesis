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

    // Assertion to ensure the invariants hold before the loop
    assert forall|i: int| 0 <= i < arr.len() ==> max_val >= arr[i] && min_val <= arr[i] by {
        if i == 0 {
            // This assertion is valid because initially both min_val and max_val are set to arr[0]
            assert(max_val >= arr[0] && min_val <= arr[0]);
        } else {
            // This should be proven in the loop invariants
        }
    };
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            1 <= arr.len(),
            exists|i: int| 0 <= i < index && max_val == arr[i],
            exists|i: int| 0 <= i < index && min_val == arr[i],
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < index ==> max_val >= arr[i], // Updated invariant to cover every element up to the current index
            // This invariant was updated because max_val is supposed to be the maximum up to the current index
            forall|i: int| 0 <= i < index ==> min_val <= arr[i], // Updated invariant to cover every element up to the current index
            // This invariant was updated because min_val is supposed to be the minimum up to the current index
            index <= arr.len(),
            min_val <= max_val,
            arr.len() == arr.len(), // Added invariant specifying the length of the array
            
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        proof {
            assert forall|i: int| 0 <= i <= index ==> max_val >= arr[i] && min_val <= arr[i] by {
                if i == index {
                    // If this is the current index, we ensure that the min and max values are updated correctly
                    assert(max_val >= arr[( index ) as int]);
                    assert(min_val <= arr[( index ) as int]);
                } else {
                    // For all previous elements, the assertion holds by the invariant
                }
            };
        }
        index += 1;
    }
    max_val - min_val
}

} // verus!



//     assert forall|i: int| 0 <= i < arr.len() ==> max_val >= arr[i] && min_val <= arr[i] by {
//   assertion failed: 0 <= i < arr.len() ==> max_val >= arr[i] && min_val <= arr[i]

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: True