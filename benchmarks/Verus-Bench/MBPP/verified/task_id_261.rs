use vstd::prelude::*;

fn main() {
    //Write a function in Rust that takes in two sequences and performs mathematical division operation element-wise across the given sequences.

    assert_eq!(
        element_wise_division(&vec![10, 4, 6, 9], &vec![5, 2, 3, 3]),
        [2, 2, 2, 3]
    );
    assert_eq!(
        element_wise_division(&vec![12, 6, 8, 16], &vec![6, 3, 4, 4]),
        [2, 2, 2, 4]
    );
    assert_eq!(
        element_wise_division(&vec![20, 14, 36, 18], &vec![5, 7, 6, 9]),
        [4, 2, 6, 2]
    );
}

verus! {

fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());

    let mut index = 0;

    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
            forall|m: int|
                0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                    <= u32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] / arr2[k]),
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!
