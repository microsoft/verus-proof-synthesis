
use vstd::prelude::*;
fn main() {}

verus! {

spec fn contains_spec(arr: Seq<i32>, key: i32) -> bool {
    exists |i: int| 0 <= i < arr.len() && (arr.index(i) == key)
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == contains_spec(arr@, key),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            forall|k: int| 0 <= k < index ==> arr[k] != key,
    {
        if arr[index] == key {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < arr1.len() ==> !contains_spec(arr2@, arr1[i]) ==> result.ghost_view().contains(arr1[i]),
        forall|i: int| 0 <= i < arr2.len() ==> !contains_spec(arr1@, arr2[i]) ==> result.ghost_view().contains(arr2[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            index <= arr1.len(),
            forall|i: int| 0 <= i < index ==> !contains_spec(arr2@, arr1[i]) ==> result.ghost_view().contains(arr1[i]),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
            result.push(arr1[index]);
        }
        index += 1;
    }

    index = 0;
    while index < arr2.len()
        invariant
            index <= arr2.len(),
            forall|i: int| 0 <= i < arr1.len() ==> !contains_spec(arr2@, arr1[i]) ==> result.ghost_view().contains(arr1[i]),
            forall|i: int| 0 <= i < index ==> !contains_spec(arr1@, arr2[i]) ==> result.ghost_view().contains(arr2[i]),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        if !contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgy_u269b`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False