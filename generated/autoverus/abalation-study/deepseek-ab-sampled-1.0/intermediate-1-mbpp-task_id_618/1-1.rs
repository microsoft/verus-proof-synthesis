
use vstd::prelude::*;

fn main() {}

verus! {

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;

    // Verify that the input vectors have the same length and are non-empty.
    verify(arr1.len() == arr2.len());

    while index < arr1.len()
        invariant
            index <= arr1.len(),
            index <= output_arr.len(),
            output_arr.len() == index,
            forall |j: int| 0 <= j < index ==>
                output_arr[j] == (arr1[j] / arr2[j]),
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }

    // Ensure the final output array meets the specified conditions.
    verify(output_arr.len() == arr1.len());

    output_arr
}

}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2