
use vstd::prelude::*;

fn main() {}

verus! {

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= arr1[i] / arr2[i]) && (arr1[i] / arr2[i] <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> result[i] == (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            output_arr.len() == index,
            output_arr.len() <= arr1.len(),
            arr1.len() == arr2.len(),
            forall |i:int| 0 <= i < index ==> output_arr[i] == arr1[i] / arr2[i],
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;

        proof {
            assert!(index <= arr1.len());
        }
    }
    output_arr
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1