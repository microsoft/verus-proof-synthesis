
use vstd::prelude::*;
fn main() {}
verus! {
    
#[verifier::loop_isolation(false)]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    let len = arr.len(); // Store the array length to use in the loop invariant
    while i < len
        invariant
            exists|j: int| 0 <= j < i ==> arr[j] != key,
            i <= len,
            arr.len() == len, // Loop invariant for array length
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

#[verifier::loop_isolation(false)]
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && #[trigger] (arr2@.contains(arr1[k])),
{
    let mut index = 0;
    let len1 = arr1.len(); // Store the array lengths to use in the loop invariants
    let len2 = arr2.len();
    while index < len1
        invariant
            !exists|j: int| 0 <= j < index && arr2@.contains(arr1[j]),
            index <= len1,
            arr1.len() == len1, // Loop invariant for array length
            arr2.len() == len2, // Loop invariant for array length
    {
        if contains(arr2, arr1[index]) {
            return true;
        }
        index += 1;
    }
    false
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpuessggi0`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False