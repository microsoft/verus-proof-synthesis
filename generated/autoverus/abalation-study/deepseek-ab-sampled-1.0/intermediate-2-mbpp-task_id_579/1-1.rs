

use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len() {
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
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    
    // First loop: iterating over arr1
    while (index < arr1.len())
        invariant
            0 <= index <= arr1.len(),
            result.len() <= arr1.len(),
            // result contains elements that are in arr1 but not in arr2 and are unique
            forall|i: int| 0 <= i < index ==> !arr2@.contains(arr1[i]) ==> result@.contains(arr1[i]),
            // Ensure all elements in result are unique and satisfy the condition
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        // Additional conditions to support the proof
        let mut i = 0;
        while (i < index)
            invariant
                0 <= i <= index,
                0 <= i < arr1.len() ==> !arr2@.contains(arr1[i]) ==> result@.contains(arr1[i]),
            {
                i += 1;
            }
        // Ensure that after processing, the result is correctly built
        i = 0;
        while (i < result.len())
            invariant
                0 <= i <= result.len(),
                result[i] == arr1[i] && !arr2@.contains(result[i]),
            {
                i += 1;
            }
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }

    index = 0;
    // Second loop: iterating over arr2
    while (index < arr2.len())
        invariant
            0 <= index <= arr2.len(),
            result.len() <= arr1.len() + arr2.len(),
            // result contains elements from arr2 that are not in arr1 and are unique
            forall|i: int| 0 <= i < index ==> !arr1@.contains(arr2[i]) ==> result@.contains(arr2[i]),
            // Ensure all elements in result are unique and satisfy the condition
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        // Additional conditions to support the proof
        let mut i = 0;
        while (i < index)
            invariant
                0 <= i <= index,
                0 <= i < arr2.len() ==> !arr1@.contains(arr2[i]) ==> result@.contains(arr2[i]),
            {
                i += 1;
            }
        // Ensure that after processing, the result is correctly built
        i = 0;
        while (i < result.len())
            invariant
                0 <= i <= result.len(),
                (result[i] == arr1[i] && !arr2@.contains(result[i])) || (result[i] == arr2[i] && !arr1@.contains(result[i])),
            {
                i += 1;
            }
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    
    result
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1