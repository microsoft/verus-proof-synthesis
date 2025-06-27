
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn contains(arr: &Seq<int>, key: int) -> bool {
        exists|i: int| 0 <= i < arr.len() && arr[i] == key
    }

    fn contains_fn(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == contains(&arr@, key as int),
    {
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                exists|k: int| 0 <= k < index ==> arr[k] != key,
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
            forall|i: int| 0 <= i < arr1.len() ==> (!contains(&arr2@, arr1[i] as int) ==> contains(&result@, arr1[i] as int)),
            forall|i: int| 0 <= i < arr2.len() ==> (!contains(&arr1@, arr2[i] as int) ==> contains(&result@, arr2[i] as int)),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    {
        let mut result = Vec::new();

        let mut index = 0;
        while index < arr1.len()
            invariant
                index <= arr1.len(),
                arr1.len() == arr1.len(),
                result.len() <= arr1.len() + arr2.len(),
                forall|i: int| 0 <= i < index ==> (!contains(&arr2@, arr1[i] as int) ==> contains(&result@, arr1[i] as int)),
                forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
        {
            if (!contains_fn(arr2, arr1[index]) && !contains_fn(&result, arr1[index])) {
                result.push(arr1[index]);
            }
            index += 1;
        }

        let mut index = 0;
        while index < arr2.len()
            invariant
                index <= arr2.len(),
                arr2.len() == arr2.len(),
                result.len() <= arr1.len() + arr2.len(),
                forall|i: int| 0 <= i < arr1.len() ==> (!contains(&arr2@, arr1[i] as int) ==> contains(&result@, arr1[i] as int)),
                forall|i: int| 0 <= i < index ==> (!contains(&arr1@, arr2[i] as int) ==> contains(&result@, arr2[i] as int)),
                forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
        {
            if (!contains_fn(arr1, arr2[index]) && !contains_fn(&result, arr2[index])) {
                result.push(arr2[index]);
            }
            index += 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpljkm5fvo`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 13
// Safe: False