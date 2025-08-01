
use vstd::prelude::*;

fn main() {}

verus! {

    fn element_wise_multiplication(
        arr1: &Vec<i32>, 
        arr2: &Vec<i32>
    ) -> (result: Vec<i32>)
        requires
            arr1.len() == arr2.len(),
            forall |i: int|
                0 <= i < arr1.len() ==>
                (i32::MIN <= (arr1[i] * arr2[i]) <= i32::MAX),
        ensures
            result.len() == arr1.len(),
            forall |i: int|
                0 <= i < result.len() ==>
                result[i] == (arr1[i] * arr2[i]),
    {
        let mut output_arr = Vec::with_capacity(arr1.len());
        let mut index = 0;
        while index < arr1.len() {
            invariant
                index <= arr1.len(),
                output_arr.len() == index,
                forall |k: int|
                    0 <= k < index ==>
                    output_arr[k] == (arr1[k] * arr2[k]),
                arr1.len() == arr2.len(),
                if index < arr1.len() then
                    i32::MIN <= (arr1[index] * arr2[index]) <= i32::MAX
                else
                    true,
            {
                // Loop body remains unchanged
                output_arr.push(arr1[index] * arr2[index]);
                index += 1;
            }
        }
        output_arr
    }

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1