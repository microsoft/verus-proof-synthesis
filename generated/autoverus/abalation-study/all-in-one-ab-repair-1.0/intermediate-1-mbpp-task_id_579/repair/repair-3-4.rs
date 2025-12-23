
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
                exists|k: int| 0 <= k < index && arr[k] != key,
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

    #[verifier::spec]
    fn is_in<T: PartialEq>(arr: &Seq<T>, element: T) -> bool {
        exists|i: int| 0 <= i < arr.len() && arr[i] == element
    }

    fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < arr1.len() ==> (!is_in(&arr2@, arr1[i]) ==> result@.contains(arr1[i])),
            forall|i: int|
                0 <= i < arr2.len() ==> (!is_in(&arr1@, arr2[i]) ==> result@.contains(arr2[i])),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> result[i] != result[j],
    {
        let mut result = Vec::new();
        let mut index = 0;
        while index < arr1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (!is_in(&arr2@, arr1[i]) ==> result@.contains(arr1[i])),
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

        let mut idx = 0;
        while idx < arr2.len()
            invariant
                forall|i: int|
                    0 <= i < arr1.len() ==> (!is_in(&arr2@, arr1[i]) ==> result@.contains(arr1[i])),
                forall|i: int|
                    0 <= i < idx ==> (!is_in(&arr1@, arr2[i]) ==> result@.contains(arr2[i])),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> result[k] != result[l],
                idx <= arr2.len(),
                arr2.len() == arr2.len(),
                result.len() == result.len(),
        {
            if !contains(arr1, arr2[idx]) && !contains(&result, arr2[idx]) {
                result.push(arr2[idx]);
            }
            idx += 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpddsxp3df`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False