use vstd::prelude::*;

fn main() {
    // Write a function in Rust takes as input two lists [a_1,...,a_n], [b_1,...,b_n] and returns [a_1+b_1,...,a_n+b_n].

    assert_eq!(add_list(&vec![10, 20, 30], &vec![15, 25, 35]), [25, 45, 65]);
    assert_eq!(add_list(&vec![1, 2, 3], &vec![5, 6, 7]), [6, 8, 10]);
    assert_eq!(
        add_list(&vec![15, 20, 30], &vec![15, 45, 75]),
        [30, 65, 105]
    );
}

verus! {

fn add_list(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] + arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] + arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] + arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] + arr2[k]),
    {
        output_arr.push((arr1[index] + arr2[index]));
        index += 1;
    }
    output_arr
}

} // verus!
