
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn contains(arr: Seq<i32>, key: i32) -> bool {
        exists|i: int| 0 <= i < arr.len() && arr[i] == key
    }

    fn contains_fn(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result <==> contains(arr@, key),
    {
        let mut i = 0;
        while i < arr.len()
            invariant
                forall|j: int| 0 <= j < i ==> arr[j] != key,
                i <= arr.len(),
        {
            if arr[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(#[trigger] result[i])),
            forall|i: int|
                0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(#[trigger] arr1[i])),
    {
        let mut output_str = Vec::new();
        let mut index = 0;
        
        while index < arr1.len()
            invariant
                forall|j: int|
                    0 <= j < index ==> (arr2@.contains(#[trigger] arr1[j]) || output_str@.contains(#[trigger] arr1[j])),
                forall|j: int|
                    0 <= j < output_str.len() ==> (arr1@.contains(#[trigger] output_str[j]) && !arr2@.contains(#[trigger] output_str[j])),
                index <= arr1.len(),
                output_str.len() <= arr1.len(),
        {
            if !contains_fn(arr2, arr1[index]) {
                output_str.push(arr1[index]);
            }
            index += 1;
        }
        output_str
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8_ik_p65`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2
// Safe: False