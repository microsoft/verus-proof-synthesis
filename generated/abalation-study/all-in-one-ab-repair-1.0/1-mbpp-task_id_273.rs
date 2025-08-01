
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= # [trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> # [trigger] result[i] == # [trigger] (arr1[i] - arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < index ==> output_arr[i] == arr1[i] - arr2[i],
            index <= arr1.len(),
            output_arr.len() == index,
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // arr1 is not modified in the loop
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // arr2 is not modified in the loop
    {
        output_arr.push((arr1[index] - arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2
// Score: (1, 0)
// Safe: True