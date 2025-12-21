use vstd::prelude::*;

fn main() {
    // Write a function in Rust which takes two integer arrays of the same length and performs the element wise modulo.

    assert_eq!(
        element_wise_module(&vec![10, 4, 5, 6], &vec![5, 6, 7, 5]),
        [0, 4, 5, 1]
    );
    assert_eq!(
        element_wise_module(&vec![11, 5, 6, 7], &vec![6, 7, 8, 6]),
        [5, 5, 6, 1]
    );
    assert_eq!(
        element_wise_module(&vec![12, 6, 7, 8], &vec![7, 8, 9, 7]),
        [5, 6, 7, 1]
    );
}

verus! {

fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] % arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
            forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] % arr2[k]),
    {
        output_arr.push((arr1[index] % arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!
