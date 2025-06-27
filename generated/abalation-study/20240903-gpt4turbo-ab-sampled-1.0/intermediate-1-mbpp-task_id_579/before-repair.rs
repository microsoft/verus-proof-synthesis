
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
            // As arr is not modified in this loop, we ensure the invariant covers every element seen so far.
            forall |j: int| 0 <= j < index ==> arr[j] != key,
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
    while index < arr1.len()
        invariant
            index <= arr1.len(),
            // As the result array is being modified in this loop, the invariant related to arr1 remains unchanged.
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    
    index = 0;
    while index < arr2.len()
        invariant
            index <= arr2.len(),
            forall |i:int| 0 <= i < index ==>
                (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i])),
                // As result array is being modified in this loop, we ensure the invariant reflects that every checked element thus far meets the condition.
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 3