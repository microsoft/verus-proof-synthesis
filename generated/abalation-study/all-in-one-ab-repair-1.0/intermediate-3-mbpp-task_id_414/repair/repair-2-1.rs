
use vstd::prelude::*;
fn main() {}

verus! {
    
    #[verifier::loop_isolation(false)]
    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut i = 0;
        while i < arr.len()
            invariant
                exists|j: int| !(0 <= j < i) || arr[j] != key, // Ensure that key is not before i
                i <= arr.len(),
                arr.len() == arr.len(), // Loop invariant for array length
        {
            if arr[i] == key {
                proof {
                    // After finding key, need to establish the postcondition
                    assert(exists|j: int| 0 <= j < arr.len() && arr[j] == key);
                }
                return true;
            }
            i += 1;
        }
        proof {
            // If loop completes, key was not found in array
            assert(!exists|j: int| 0 <= j < arr.len() && arr[j] == key);
        }
        false
    }

    fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
        ensures
            result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
    {
        let mut index = 0;
        while index < arr1.len()
            invariant
                !(exists|j: int| 0 <= j < index && arr2@.contains(arr1[j])), // Ensure that no earlier index in arr1 is in arr2
                index <= arr1.len(),
                arr1.len() == arr1.len(), // Loop invariant for array length
                arr2.len() == arr2.len(), // Loop invariant for array length
        {
            if contains(arr2, arr1[index]) {
                proof {
                    // After finding matching value, establish the postcondition
                    assert(exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k]));
                }
                return true;
            }
            index += 1;
        }
        proof {
            // If loop completes, no element of arr1 is in arr2
            assert(!exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k]));
        }
        false
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpt5842apf`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False