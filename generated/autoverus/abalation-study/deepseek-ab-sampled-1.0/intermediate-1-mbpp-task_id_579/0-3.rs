
use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while (index < arr.len()) 
        invariant 
            index <= arr.len(),
            contains@.loop_invariants::specifies_correct_behavior(arr, index, key),
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
            result.len() <= arr1.len() + arr2.len(),
            ensure_unique_elements(arr1, result, index, arr2),
    {
        if (!contains(arr2, arr1[index]) && !contains,&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    while (index < arr2.len())
        invariant 
            index <= arr2.len(),
            result.len() <= arr1.len() + arr2.len(),
            ensure_unique_elements(arr2, result, index, arr1),
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

// Additional spec functions for invariants
spec fn contains@.loop_invariants::specifies_correct_behavior(arr: &Vec<i32>, index: usize, key: i32) bool {
    // Ensure that the index is within bounds and the loop checks each element correctly
    index <= arr.len() && 
    (forall|i: int| 0 <= i < index as int ==> arr[i as usize] != key) ==>
    index == arr.len() || !arr[index].equals(key)
}

spec fn ensure_unique_elements(arr_current: &Vec<i32>, result: Vec<i32>, index: usize, arr_other: &Vec<i32>) bool {
    // Ensure that elements added to the result are unique and meet the dissimilar condition
    forall|i: int| 0 <= i < arr_current.len() as int ==> 
        (arr_current[i as usize] == result[i as usize] ==> 
            !arr_other.contains(result[i as usize]) && 
            !result[..i as usize].contains(result[i as usize]))
}
} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2