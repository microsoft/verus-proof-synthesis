
use vstd::prelude::*;
fn main() {}
verus! {

fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= # [trigger] (arr1[i] % arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> # [trigger] result[i] == # [trigger] (arr1[i] % arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|k: int|
                0 <= k < index ==> # [trigger] output_arr[k] == # [trigger] (arr1[k] % arr2[k]),
            output_arr.len() == index,
    {
        assert(0 <= arr1[( index ) as int] % arr2[( index ) as int] <= u32::MAX) by (nonlinear_arith) requires arr1[( index ) as int] != u32::MAX + 1, arr2[( index ) as int] != 0, {}

        output_arr.push((arr1[index] % arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!






// Score: (0, 1)
// Safe: True