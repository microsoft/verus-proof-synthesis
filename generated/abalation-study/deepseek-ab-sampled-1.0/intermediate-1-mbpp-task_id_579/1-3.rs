
use vstd::prelude::*;

fn main() {}

verus! {

#[spec fn]
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
        // Elements from arr1 not in arr2 are in result
        forall|i: int| 0 <= i < arr1.len() 
            ==> (!contains(arr2, arr1[i]) ==> contains(&result, arr1[i])),
        // Elements from arr2 not in arr1 are in result
        forall|i: int| 0 <= i < arr2.len()
            ==> (!contains(arr1, arr2[i]) ==> contains(&result, arr2[i])),
        // All elements in result are unique
        forall|i: int, j: int|
            0 <= i < j < result.len() 
            ==> result[i] != result[j],
        // If arr1 and arr2 have no common elements, result is combination
        (forall|i: int| 0 <= i < arr1.len() 
            ==> contains(arr2, arr1[i]))
        ==> result == Vec::new(),
        // No duplicates in arr1 or arr2 affect the result
        forall|x: i32| x occurs in result <= 1,
    ensures
        // The result includes all elements from arr1 not in arr2
        result == arr1@.filter(|x| !arr2@.contains(x))
                    .concat(arr2@.filter(|x| !arr1@.contains(x))),
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len() {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    while index < arr2.len() {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1