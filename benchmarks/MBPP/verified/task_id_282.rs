use vstd::prelude::*;

fn main() {
    // Write a function in Rust to subtract two lists element-wise.

    assert_eq!(
        element_wise_subtract(&vec![1, 2, 3], &vec![4, 5, 6]),
        [-3, -3, -3]
    );
    assert_eq!(element_wise_subtract(&vec![1, 2], &vec![3, 4]), [-2, -2]);
    assert_eq!(
        element_wise_subtract(&vec![90, 120], &vec![50, 70]),
        [40, 50]
    );
}

verus! {

fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] - arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());

    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] - arr2[k]),
    {
        output_arr.push((arr1[index] - arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!
