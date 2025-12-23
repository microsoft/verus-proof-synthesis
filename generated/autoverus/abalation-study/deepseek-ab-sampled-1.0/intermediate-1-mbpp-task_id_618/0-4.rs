

use vstd::prelude::*;

fn main() {}

verus! {

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall |i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
    ensures
        result@.len() == arr1@.len(),
        forall |i: int| 0 <= i < result.len() ==> result[i] == arr1[i] / arr2[i],
{
    let n = arr1.len();
    let mut output_arr = Vec::new();
    let mut index = 0;

    while (index < n)
        invariant
            index <= n,
            output_arr.len() == index,
            arr1.len() == n,
            arr2.len() == n,
            forall |i: int| 0 <= i < index ==> output_arr[i] == arr1[i] / arr2[i],
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }

    output_arr
}

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1