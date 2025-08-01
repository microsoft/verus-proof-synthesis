
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
            exists|k: int| 0 <= k < index ==> arr[k] != key,
            index <= arr.len(),
            arr.len() == old(arr.len()),   // Loop invariant specifying the length of the array
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
            forall|i: int|
                0 <= i < index ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                    arr1[i],
                )),
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> # [trigger] result[k] != # [trigger] result[l],
            index <= arr1.len(),
            arr1.len() == old(arr1.len()), // Loop invariant specifying the length of arr1
            result.len() <= index, // Ensure result length grows correctly
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    index = 0;
    while index < arr2.len()
        invariant
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                    arr1[i],
                )),
            forall|i: int|
                0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
                    arr2[i],
                )),
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> # [trigger] result[k] != # [trigger] result[l],
            index <= arr2.len(),
            arr2.len() == old(arr2.len()), // Loop invariant specifying the length of arr2
            result.len() <= index + arr1.len(), // Ensure result length grows correctly
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpr70ogq4r`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False