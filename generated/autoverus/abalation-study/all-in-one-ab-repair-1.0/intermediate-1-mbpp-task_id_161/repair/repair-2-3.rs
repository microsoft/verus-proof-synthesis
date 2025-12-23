
use vstd::prelude::*;
fn main() {}

verus! {

// Function to check if a key exists in the array
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < arr.len() && { arr[i] == key }),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            // Key cannot appear in any of the checked indices before i
            forall|j: int| 0 <= j < i ==> arr[j] != key,
            // i is within bounds of the array
            i <= arr.len(),
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

// Function to remove elements from arr1 that are present in arr2
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        // All elements in the result are in arr1 and not in arr2
        forall|i: int| 0 <= i < result.len() ==> arr1@.contains(result[i]) && !arr2@.contains(result[i]),
        // All elements in arr1 are either in arr2 or in the result
        forall|i: int| 0 <= i < arr1.len() ==> arr2@.contains(arr1[i]) || result@.contains(arr1[i]),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            // All indexes checked so far satisfy the condition
            forall|j: int| 0 <= j < index ==> arr2@.contains(arr1[j]) || output_str@.contains(arr1[j]),
            // All elements in the output_str satisfy the condition
            forall|j: int| 0 <= j < output_str.len() ==> arr1@.contains(output_str[j]) && !arr2@.contains(output_str[j]),
            // Index is within bounds
            index <= arr1.len(),
    {
        // Add element to output_str if not in arr2
        if !contains(arr2, arr1[index]) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpm44efafz`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: False