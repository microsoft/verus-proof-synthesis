use vstd::prelude::*;
fn main() {}
verus! {

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= # [trigger] (arr1[i] / arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> # [trigger] result[i] == # [trigger] (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 < arr1.len() < 1000,
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < index ==> arr2[i] != 0,
            forall|i: int|
                0 <= i < index as int ==> output_arr[i as int] == arr1[i as int] / arr2[i as int],
            forall|i: int| 0 <= i < output_arr.len() ==> output_arr[i] == (arr1[i] / arr2[i]),
            index < arr1.len(),
            index <= arr1.len(),
            output_arr.len() == index,
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 5