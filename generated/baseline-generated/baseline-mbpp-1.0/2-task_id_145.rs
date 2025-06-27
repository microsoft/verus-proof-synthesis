use vstd::prelude::*;

fn main() {}

verus! {

fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];

    let mut index = 1;

    // Proof block before the loop
    proof {
        assert(arr.len() > 0);
    } // Added by AI

    while index < arr.len()
        invariant
            1 <= index <= arr.len(), // Constraint on index
            exists |k: int| 0 <= k < index && min_val == arr[k], // min_val is the minimum value seen so far
            exists |k: int| 0 <= k < index && max_val == arr[k], // max_val is the maximum value seen so far
            forall|i: int, j: int| 0 <= i < index && 0 <= j < index ==> arr[i] - arr[j] <= max_val - min_val, // diff invariant
    {
        if arr[index] < min_val {
            min_val = arr[index];
        } 
        else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }

    // Proof block after the loop
    proof {
        assert(forall |i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= max_val - min_val);
    } // Added by AI

    max_val - min_val
}

} // verus!
// Score: (2, 0)
// Safe: False