
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::spec]
    fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;
        while i < str.len()
            invariant
                forall|j: int| 0 <= j < i ==> str[j] != key,
                i <= str.len(),
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    #[verifier::spec]
    fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(#[trigger] result[i])),
            forall|i: int|
                0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(#[trigger] arr1[i])),
    {
        let mut output_arr = Vec::new();
        let mut index: usize = 0;
        while index < arr1.len()
            invariant
                forall|j: int|
                    0 <= j < index ==> (arr2@.contains(#[trigger] arr1[j]) || output_arr@.contains(#[trigger] arr1[j])),
                forall|j: int|
                    0 <= j < output_arr.len() ==> (arr1@.contains(#[trigger] output_arr[j]) && !arr2@.contains(#[trigger] output_arr[j])),
                index <= arr1.len(),
                output_arr.len() <= index,
                arr1.len() == arr1.len(),
        {
            if !contains(arr2, arr1[index]) {
                output_arr.push(arr1[index]);
            }
            index += 1;
        }
        output_arr
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpqmn904hs`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False