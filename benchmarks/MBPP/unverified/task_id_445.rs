use vstd::prelude::*;

fn main() {}

verus! {

fn element_wise_multiplication(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] * arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len() {
        output_arr.push((arr1[index] * arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!
