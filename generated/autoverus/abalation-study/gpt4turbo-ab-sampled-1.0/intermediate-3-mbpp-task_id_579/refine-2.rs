
use vstd::prelude::*;
fn main() {}
verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|i: int| 0 <= i < index ==> (arr[i] != key),
            arr.len() == arr.len(), // Loop invariant for array `arr`
            // Since `arr` is never modified in this loop, we can assert that the loop invariant covers all elements up to `index`.
            // However, no change is needed as the invariant correctly reflects the loop's behavior without modification.
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
            forall|i: int|
                0 <= i < index ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
            index <= arr1.len(),
            arr1.len() == arr1.len(), // Loop invariant for array `arr1`
            result.len() <= arr1.len() + arr2.len(), // Loop invariant for array `result`
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    while index < arr2.len()
        invariant
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
            forall|i: int|
                0 <= i < index ==> (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i])),
            index <= arr2.len(),
            arr2.len() == arr2.len(), // Loop invariant for array `arr2`
            // Because no elements are added to `arr2` within this loop, all elements are covered.
            result.len() <= arr1.len() + arr2.len(), // Loop invariant for array `result`
            // Because no elements are added to `result` outside of conditions checked in this loop, it satisfies the requirements.
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!
