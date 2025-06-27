
use vstd::prelude::*;
fn main() {}

verus! {
    // contains function to check if an element exists in a Vec
    fn contains(arr: &Vec<i32>, key: i32) -> bool
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                arr.len() == old(arr).len(),
                forall|k: int| 0 <= k < index ==> arr[k] != key
        {
            if arr[index] == key {
                return true;
            }
            index += 1;
        }
        false
    }

    // find_dissimilar function to find dissimilar elements between two Vecs
    fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int| 0 <= i < arr1.len() ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
            forall|i: int| 0 <= i < arr2.len() ==> (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i])),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    {
        let mut result = Vec::new();
        let mut index = 0;
        
        while index < arr1.len()
            invariant
                forall|i: int| 0 <= i < index ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
                forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr1.len(),
                arr1.len() == old(arr1).len(),
                result@.len() <= arr1.len() + arr2.len(),
                result@ == result@, // Loop invariant specifying the unchanged nature of result@ Seq
        {
            if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
                result.push(arr1[index]);
            }
            index += 1;
        }

        let mut index = 0;
        while index < arr2.len()
            invariant
                forall|i: int| 0 <= i < arr1.len() ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])),
                forall|i: int| 0 <= i < index ==> (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i])),
                forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr2.len(),
                arr2.len() == old(arr2).len(),
                result@.len() <= arr1.len() + arr2.len(),
                result@ == result@, // Loop invariant specifying the unchanged nature of result@ Seq
        {
            if !contains(arr1, arr2[index]) && !contains(&result, arr2[index]) {
                result.push(arr2[index]);
            }
            index += 1;
        }

        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpodhod0t1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False