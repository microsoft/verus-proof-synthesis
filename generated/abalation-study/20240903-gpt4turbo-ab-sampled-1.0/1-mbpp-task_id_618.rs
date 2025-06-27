
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        // Since arr1 and arr2 are not modified in this function, their properties can apply to all elements.
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= # [trigger] (arr1[i] / arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        // since the result array is being constructed to match arr1[i] / arr2[i], this invariant covers the entire arrays.
        forall|i: int|
            0 <= i < result.len() ==> # [trigger] result[i] == # [trigger] (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            // Explanation: This invariant ensures that each element added to output_arr until the current index 
            // matches the division of the corresponding elements in arr1 and arr2, which are not modified in the loop.
            forall|i: int| 0 <= i < index ==> output_arr@[i] == (arr1[i] / arr2[i]),
            index <= arr1.len(),
            // This loop invariant makes sure the size of output_arr matches the current index,
            // indicating the number of elements processed and added to output_arr.
            output_arr.len() == index,
    {
        // No changes were required based on the provided instructions for this specific task.
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!
// Score: (1, 0)
// Safe: True