
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
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
            forall|i: int|
                0 <= i < arr2.len() ==> (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i])),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> result[i] != result[j],
    {
        let mut result = Vec::new();
        let mut index = 0;
        while index < arr1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr1.len(),
                arr1.len() == arr1.len(),
                result.len() == result.len(),
        {
            if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
                result.push(arr1[index]);
            }
            index += 1;
        }
        index = 0;  // Reset index to be used for arr2
        while index < arr2.len()
            invariant
                forall|i: int|
                    0 <= i < arr1.len() ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
                forall|i: int|
                    0 <= i < index ==> (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i])),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr2.len(),
                arr2.len() == arr2.len(),
                result.len() == result.len(),
        {
            if !contains(arr1, arr2[index]) && !contains(&result, arr2[index]) {
                result.push(arr2[index]);
            }
            index += 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpinyhy87m`)
// 

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: False