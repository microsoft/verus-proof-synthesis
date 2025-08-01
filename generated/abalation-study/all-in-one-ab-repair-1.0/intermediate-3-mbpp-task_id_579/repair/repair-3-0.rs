
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|k: int| 0 <= k < index ==> arr[k] != key,
            index <= arr.len(),
            arr.len() == arr.len(),   // Loop invariant specifying the length of the array
    {
        if arr[index] == key {
            return true;
        }
        index += 1;
    }
    false
}

// Helper function to check if a Seq contains a value.
spec fn seq_contains<T>(seq: Seq<T>, value: T) -> bool 
    where T: PartialEq
{
    exists|i: int| 0 <= i < seq.len() && seq[i] == value
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        // Ensuring that the result contains elements from arr1 that are not in arr2
        forall|i: int|
            0 <= i < arr1.len() ==> (!seq_contains(arr2@, arr1[i]) ==> seq_contains(result@, arr1[i])),
        
        // Ensuring that the result contains elements from arr2 that are not in arr1
        forall|i: int|
            0 <= i < arr2.len() ==> (!seq_contains(arr1@, arr2[i]) ==> seq_contains(result@, arr2[i])),
        
        // Ensuring all elements in result are unique
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut result = Vec::new();
    let mut index = 0;

    while index < arr1.len()
        invariant
            // Invariant ensuring that elements from arr1 that are not in arr2 and not already in result are added
            forall|i: int|
                0 <= i < index ==> (!seq_contains(arr2@, arr1[i]) ==> seq_contains(result@, arr1[i])),

            // Invariant for uniqueness of the result array elements
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> result[k] != result[l],

            // Maintaining the boundary condition
            index <= arr1.len(),

            // Maintaining the length of arr1
            arr1.len() == arr1.len(),

            // Maintaining the length of result
            result.len() == result@.len(),
    {
        if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
            result.push(arr1[index]);
        }
        index += 1;
    }

    let mut index = 0;
    while index < arr2.len()
        invariant
            // Ensuring the elements from arr2 that are not in arr1 and not already in result are added
            forall|i: int|
                0 <= i < arr1.len() ==> (!seq_contains(arr2@, arr1[i]) ==> seq_contains(result@, arr1[i])),
            
            // Checking the added elements from arr2
            forall|i: int|
                0 <= i < index ==> (!seq_contains(arr1@, arr2[i]) ==> seq_contains(result@, arr2[i])),

            // Invariant ensuring the uniqueness of each element in result array
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> result[k] != result[l],

            // Maintaining boundary condition
            index <= arr2.len(),

            // Maintaining length of arr2
            arr2.len() == arr2.len(),

            // Maintaining the length of result
            result.len() == result@.len(),
    {
        if !contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9ke8gyg5`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False