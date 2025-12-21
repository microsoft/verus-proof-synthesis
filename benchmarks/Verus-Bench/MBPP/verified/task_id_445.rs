use vstd::prelude::*;

fn main() {
    // Write a function in Rust to perform index wise multiplication of elements in the given two sequences.

    assert_eq!(
        element_wise_multiplication(
            &vec![1, 3, 4, 5, 2, 9, 1, 10],
            &vec![6, 7, 3, 9, 1, 1, 7, 3]
        ),
        [6, 21, 12, 45, 2, 9, 7, 30]
    );
    assert_eq!(
        element_wise_multiplication(
            &vec![2, 4, 5, 6, 3, 10, 2, 11],
            &vec![7, 8, 4, 10, 2, 2, 8, 4]
        ),
        [14, 32, 20, 60, 6, 20, 16, 44]
    );
    assert_eq!(
        element_wise_multiplication(
            &vec![3, 5, 6, 7, 4, 11, 3, 12],
            &vec![8, 9, 5, 11, 3, 3, 9, 5]
        ),
        [24, 45, 30, 77, 12, 33, 27, 60]
    );
}

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
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] * arr2[k]),
    {
        output_arr.push((arr1[index] * arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!
