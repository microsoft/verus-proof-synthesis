

use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
    {
        if (arr[index] == key)
        {
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
    while (index < arr1.len())
        invariant
            index <= arr1.len(),
            0 <= index <= arr1.len(),
            arr1.len() >= 0,
            0 <= arr1.len(),
            arr2.len() >= 0,
            0 <= arr2.len(),
            0 <= result.len(),
            result.len() <= arr1.len() + arr2.len(),
            forall |i: int, j: int| 0 <= i < result.len() && i != j ==> result[i] != result[j], 
            // This invariant ensures all elements in 'result' are unique.
            0 <= index, 
            arr1.len() >= 0, 
            arr2.len() >= 0,
            exists |k: int| 0 <= k < arr1.len() && !arr2@.contains(arr1[k]) ==> result@.contains(arr1[k]),
            // This invariant ensures that for any element in arr1 not found in arr2, it's added to 'result'.
            exists |k: int| 0 <= k < index && !arr2@.contains(arr1[k]) && !result@.contains(arr1[k]) ==> result@.contains(arr1[k])
        {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index]))
        {
            result.push(arr1[index]);
        }

        index += 1;
    }

    index = 0;
    while (index < arr2.len())
        invariant
            index <= arr2.len(),
            arr2.len() >= 0,
            arr1.len() >= 0,
            0 <= index < arr2.len(),
            0 <= result.len(),
            result.len() <= arr1.len() + arr2.len(),
            forall |i: int, j: int| 0 <= i < result.len() && i != j ==> result[i] != result[j], 
            // Maintaining the uniqueness invariant.
            0 <= index, 
            arr2.len() >= 0,
            0 <= arr2.len(),
            0 <= arr1.len(),
            0 <= arr2.len(),
            0 <= result.len(),
            exists |k: int| 0 <= k < arr2.len() && !arr1@.contains(arr2[k]) ==> result@.contains(arr2[k]), 
            // Ensuring elements from arr2 not in arr1 are added.
            !result@.contains(arr2[( index ) as int]) || contains(arr2, arr2[( index ) as int])
        {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index]))
        {
            result.push(arr2[index]);
        }

        index += 1;
    }

    result
}

}


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1