
use vstd::prelude::*;
fn main() {}

verus! {

spec fn contains(arr: Seq<i32>, key: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == key
}

fn contains_test(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == contains(arr@, key),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            exists|k: int| 0 <= k < index ==> arr[k] != key,
            index <= arr.len(),
            arr.len() == arr.len(),
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
        forall|i: int| 0 <= i < arr1.len() ==> (!contains(arr2@, arr1[i]) ==> #[trigger] result@.contains(arr1[i])),
        forall|i: int| 0 <= i < arr2.len() ==> (!contains(arr1@, arr2[i]) ==> #[trigger] result@.contains(arr2[i])),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|i: int| 0 <= i < index ==> (!contains(arr2@, arr1[i]) ==> #[trigger] result@.contains(arr1[i])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
            index <= arr1.len(),
            arr1.len() == arr1.len(), // Loop invariant specifying the length of arr1
            result.len() == result.len(), // Loop invariant specifying the length of result
    {
        if !contains_test(arr2, arr1[index]) && !contains_test(&result, arr1[index]) {
            result.push(arr1[index]);
        }
        index += 1;
    }

    let mut index = 0;
    while index < arr2.len()
        invariant
            forall|i: int| 0 <= i < arr1.len() ==> (!contains(arr2@, arr1[i]) ==> #[trigger] result@.contains(arr1[i])),
            forall|i: int| 0 <= i < index ==> (!contains(arr1@, arr2[i]) ==> #[trigger] result@.contains(arr2[i])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
            index <= arr2.len(),
            arr2.len() == arr2.len(), // Loop invariant specifying the length of arr2
            result.len() == result.len(), // Loop invariant specifying the length of result
    {
        if !contains_test(arr1, arr2[index]) && !contains_test(&result, arr2[index]) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp0a9gmpix`)
// 

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 5
// Safe: False