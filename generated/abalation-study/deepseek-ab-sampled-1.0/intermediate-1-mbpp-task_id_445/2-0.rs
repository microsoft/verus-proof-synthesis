

use vstd::prelude::*;

fn main() {}

verus! {

fn element_wise_multiplication(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] * arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            // The output array has the correct length based on the index
            output_arr.len() == index,
            // The index is within the valid range
            index <= arr1.len(),
            // All elements in the output array are correct so far
            (forall |j: int|
                0 <= j < index ==> output_arr[j] == arr1[j] * arr2[j]),
            // The product remains within i32 bounds for all elements processed
            (forall |j: int|
                0 <= j < index ==> i32::MIN <= output_arr[j] <= i32::MAX),
    {
        output_arr.push(arr1[index] * arr2[index]);
        index += 1;
    }
    output_arr
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1