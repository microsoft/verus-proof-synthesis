
use vstd::prelude::*;
fn main() {}
verus! {

fn element_wise_multiplication(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= # [trigger] (arr1[i] * arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> # [trigger] result[i] == # [trigger] (arr1[i] * arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
            forall|i: int|
                0 <= i < index ==> # [trigger] output_arr[i] == # [trigger] (arr1[i] * arr2[i]),
            // The following invariant ensures that arr1 and arr2 are not modified in the loop
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k],
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k],
            index <= arr1.len(),
            output_arr.len() == index,
    {
        assert(0 <= arr1[( index ) as int] * arr2[( index ) as int] <= i32::MAX) by (nonlinear_arith)
            requires
                0 <= index,
                index < arr1.len(),
                i32::MIN <= arr1[( index ) as int],
                arr1[( index ) as int] <= i32::MAX,
                i32::MIN <= arr2[( index ) as int],
                arr2[( index ) as int] <= i32::MAX,
                {};

        output_arr.push((arr1[index] * arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!







// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1