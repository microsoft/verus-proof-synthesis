
use vstd::prelude::*;
fn main() {}
verus! {

fn bit_wise_xor(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> result[i] == #[trigger] arr1[i] ^ #[trigger] arr2[i],
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|i: int| 0 <= i < index ==> #[trigger] output_arr[i] == arr1[i] ^ arr2[i],
            forall|i: int| 0 <= i < index ==> output_arr[i] == (arr1[i] ^ arr2[i]),
            forall|i: int| 0 <= i < index ==> output_arr[i] == arr1[i] ^ arr2[i],
            index <= arr1.len(),
            output_arr.len() == index,
            arr1.len() == arr2.len(),
    {
        output_arr.push((arr1[index] ^ arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!

// Score: (2, 0)
// Safe: True