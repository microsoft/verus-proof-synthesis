
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
                exists|j: int| 0 <= j < i ==> arr[j] != key,
                i <= arr.len(),
                arr.len() == old(arr).len(), // Fixed array length invariant
        {
            if arr[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
        ensures
            result == exists|k: int| 0 <= k < arr1.len() && #[trigger] arr2.contains(&arr1[k]),
    {
        let mut index = 0;
        while index < arr1.len()
            invariant
                !exists|j: int| 0 <= j < index && arr2.contains(&arr1[j]),
                index <= arr1.len(),
                arr1.len() == old(arr1).len(), // Fixed array length invariant
                arr2.len() == old(arr2).len(), // Fixed array length invariant
        {
            if contains(arr2, arr1[index]) {
                return true;
            }
            index += 1;
        }
        false
    }

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpvj61k66j`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False