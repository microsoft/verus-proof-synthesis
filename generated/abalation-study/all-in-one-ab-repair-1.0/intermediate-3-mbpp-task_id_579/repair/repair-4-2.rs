
use vstd::prelude::*;
fn main() {}

verus! {

spec fn seq_contains<T>(seq: Seq<T>, key: T) -> bool
    where T: Copy + Eq
{
    exists|i: int| 0 <= i < seq.len() && (seq[i] == key)
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            exists|k: int| 0 <= k < arr.len() && (arr[k] != key) ==> index <= arr.len(), // Fix invariant
            index <= arr.len(),
            arr.len() == arr.len(), // Loop invariant specifying the length of the array
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
        forall|i: int|
            0 <= i < arr1.len() ==> (!seq_contains(arr2@, arr1[i]) ==> seq_contains(result@, arr1[i])),
        forall|i: int|
            0 <= i < arr2.len() ==> (!seq_contains(arr1@, arr2[i]) ==> seq_contains(result@, arr2[i])),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (!seq_contains(arr2@, arr1[i]) ==> seq_contains(result@, arr1[i])),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> result@.index(i) != result@.index(j),
            index <= arr1.len(),
            arr1.len() == arr1.len(), // Loop invariant specifying the length of arr1
            result.len() == result@.len(), // Loop invariant specifying the length of result
    {
        if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
            result.push(arr1[index]);
        }
        index += 1;
    }

    let mut index2 = 0; // Changed from `index` to `index2` to prevent shadowing
    while index2 < arr2.len()
        invariant
            forall|i: int|
                0 <= i < arr1.len() ==> (!seq_contains(arr2@, arr1[i]) ==> seq_contains(result@, arr1[i])),
            forall|i: int|
                0 <= i < index2 ==> (!seq_contains(arr1@, arr2[i]) ==> seq_contains(result@, arr2[i])),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> result@.index(i) != result@.index(j),
            index2 <= arr2.len(),
            arr2.len() == arr2.len(), // Loop invariant specifying the length of arr2
            result.len() == result@.len(), // Loop invariant specifying the length of result
    {
        if !contains(arr1, arr2[index2]) && !contains(&result, arr2[index2]) {
            result.push(arr2[index2]);
        }
        index2 += 1;
    }
    result
}

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu_6fe7iq`)
// 

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 5
// Safe: False