use vstd::prelude::*;
fn main() {}
verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[j] != key,
            exists|j: int| 0 <= j < i ==> arr[j] != key,
            i <= arr.len(),
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && arr2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut output_arr = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|i: int, j: int| 0 <= i < j < output_arr.len() ==> output_arr[i] != output_arr[j],
            forall|i: int|
                0 <= i < output_arr.len() ==> arr1@.contains(# [trigger] output_arr[i])
                    && arr2@.contains(# [trigger] output_arr[i]),
            output_arr.len() <= arr1.len(),
            output_arr.len() <= arr2.len(),
            forall|i: int|
                0 <= i < output_arr.len() ==> (arr1@.contains(# [trigger] output_arr[i])
                    && arr2@.contains(# [trigger] output_arr[i])),
            index <= arr1.len(),
            output_arr@.len() <= arr1.len(),
    {
        if (contains(arr2, arr1[index]) && !contains(&output_arr, arr1[index])) {
            output_arr.push(arr1[index]);
        }
        index += 1;
    }
    output_arr
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4