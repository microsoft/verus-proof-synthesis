use vstd::prelude::*;

fn main() {
    // Write a function in Rust that takes in two sequences and subtracts the elements of the first sequence by the elements of the second sequence with the same index.

    assert_eq!(
        element_wise_subtract(&vec![10, 4, 5], &vec![2, 5, 18]),
        [8, -1, -13]
    );
    assert_eq!(
        element_wise_subtract(&vec![11, 2, 3], &vec![24, 45, 16]),
        [-13, -43, -13]
    );
    assert_eq!(
        element_wise_subtract(&vec![7, 18, 9], &vec![10, 11, 12]),
        [-3, 7, -3]
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
