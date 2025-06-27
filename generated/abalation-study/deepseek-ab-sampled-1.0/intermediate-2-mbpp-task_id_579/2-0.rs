

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

    // Process elements from arr1
    while (index < arr1.len())
        invariant
            0 <= index <= arr1.len(),
            arr1.len() >= 0,
            result@.len() + (arr1.len() - index) <= 1000,
            // Ensure no duplicates in the result vector
            forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@.index(i) != result@.index(j),
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
            // Maintain the invariant of unique elements in result
            assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]);
        }
        index += 1;
    }

    // Process elements from arr2
    let mut index = 0;
    while (index < arr2.len())
        invariant
            0 <= index <= arr2.len(),
            arr2.len() >= 0,
            result@.len() + (arr2.len() - index) <= 1000,
            // Ensure no duplicates in the result vector
            forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@.index(i) != result@.index(j),
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
            // Maintain the invariant of unique elements in result
            assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]);
        }
        index += 1;
    }

    result
}

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 5