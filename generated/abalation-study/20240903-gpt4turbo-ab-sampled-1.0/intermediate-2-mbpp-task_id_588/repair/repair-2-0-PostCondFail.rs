
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
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            arr.len() == arr.len(), // specifying the length of the array `arr`
            // Adjust the invariant to cover every element so far
            // Array `arr` is not modified in the loop; this invariant is adjusted to cover all processed elements.
            forall |k: int| 0 <= k < index ==> arr@[k as int] <= max_val,
            forall |k: int| 0 <= k < index ==> arr@[k as int] >= min_val,
            i32::MIN / 2 < min_val,
            max_val < i32::MAX / 2,
    {
        if (arr[index] < min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    proof {
        assert(max_rcur(arr@) == max_val); // Proof for maximum value
        assert(min_rcur(arr@) == min_val); // Proof for minimum value
    }
    max_val - min_val
}

} // verus!


// failed this postcondition
//         diff == max_rcur(arr@) - min_rcur(arr@),
// at the end of the function body
// {
//     let mut min_val = arr[0];
//     let mut max_val = arr[0];
//     let mut index = 1;
// ...
//     max_val - min_val
// }
//   at the end of the function body: {     let mut min_val = arr[0];     let mut max_val = arr[0];     let mut index = 1;     while index < arr.len()         invariant             1 <= index <= arr.len(),             arr.len() == arr.len(), // specifying the length of the array `arr`             // Adjust the invariant to cover every element so far             // Array `arr` is not modified in the loop; this invariant is adjusted to cover all processed elements.             forall |k: int| 0 <= k < index ==> arr@[k as int] <= max_val,             forall |k: int| 0 <= k < index ==> arr@[k as int] >= min_val,             i32::MIN / 2 < min_val,             max_val < i32::MAX / 2,     {         if (arr[index] <= min_val) {             min_val = arr[index];         } else if (arr[index] > max_val) {             max_val = arr[index];         }         index += 1;     }     max_val - min_val }
//   failed this postcondition: diff == max_rcur(arr@) - min_rcur(arr@)

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False