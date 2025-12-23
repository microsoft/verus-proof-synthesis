

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
                arr1@.contains(#[trigger] arr2[i]), result@.contains(
                arr2[i],
            ))),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            index <= arr1.len(),
            result.len() <= arr1.len() + arr2.len(),
            // Up to index, every element in arr1 has been checked against arr2 and result
            forall |k: int| 0 <= k < index ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            // All elements in result are unique and from arr1 or arr2
            forall |i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }

    let mut index = 0;
    while index < arr2.len()
        invariant
            index <= arr2.len(),
            result.len() <= arr1.len() + arr2.len(),
            // Up to index, every element in arr2 has been checked against arr1 and result
            forall |k: int| 0 <= k < index ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            // All elements in result are unique and from arr1 or arr2
            forall |i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
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