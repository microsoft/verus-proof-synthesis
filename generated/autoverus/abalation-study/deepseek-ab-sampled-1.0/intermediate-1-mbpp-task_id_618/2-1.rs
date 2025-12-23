

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
    let arr_len: usize = arr1.len();
    let mut output_arr = Vec::with_capacity(arr_len);
    let mut index = 0;
    while index < arr_len
        invariant
            index <= arr_len,
            arr1.len() == arr_len,
            arr2.len() == arr_len,
            elem = index: 
                |&index| 0 <= index < arr_len ==> output_arr[index] == (arr1[index] / arr2[index]),
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }
    output_arr
} // verus!
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1