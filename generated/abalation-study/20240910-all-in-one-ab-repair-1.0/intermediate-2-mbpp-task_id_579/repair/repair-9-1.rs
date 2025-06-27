
use vstd::prelude::*;
fn main() {}

verus! {
    proof fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut index = 0;
        while index < arr.len()
            invariant
                exists|k: int| 0 <= k < index ==> arr[k] != key,
                index <= arr.len(),
                arr.len() == arr.len(),   // Loop invariant specifying the length of the array
        {
            if (arr[index] == key) {
                return true;
            }
            index += 1;
        }
        false
    }

    pub fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> Vec<i32>
        ensures
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2.contains(arr1[i]) ==> result.contains(arr1[i])),
            forall|i: int|
                0 <= i < arr2.len() ==> (!arr1.contains(arr2[i]) ==> result.contains(arr2[i])),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> result[i] != result[j],
    {
        let mut result = Vec::new();
        let mut index = 0;
        
        while index < arr1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (!contains(arr2, arr1[i]) ==> result.contains(arr1[i])),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr1.len(),
                arr1.len() == arr1.len(), // Loop invariant specifying the length of arr1,
                result.len() <= arr1.len() + arr2.len(), // Providing bounds for result
        {
            if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
                result.push(arr1[index]);
                proof {
                    assert(result.len() > 0);
                    assert(result.contains(arr1[index])); // Correct assertion to compare sequences
                }
            }
            index += 1;
        }
        
        index = 0;
        while index < arr2.len()
            invariant
                forall|i: int|
                    0 <= i < arr1.len() ==> (!contains(arr2, arr1[i]) ==> result.contains(arr1[i])),
                forall|i: int|
                    0 <= i < index ==> (!contains(arr1, arr2[i]) ==> result.contains(arr2[i])),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr2.len(),
                arr2.len() == arr2.len(), // Loop invariant specifying the length of arr2
                result.len() <= arr1.len() + arr2.len(), // Providing bounds for result
        {
            if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
                result.push(arr2[index]);
                proof {
                    assert(result.len() > 0);
                    assert(result.contains(arr2[index])); // Correct assertion to compare sequences
                }
            }
            index += 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmptyi6k58j`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False