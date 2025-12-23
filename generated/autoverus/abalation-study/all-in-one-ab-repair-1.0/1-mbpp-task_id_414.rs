
use vstd::prelude::*;
fn main() {}
verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key, // all elements checked before `i` are not equal to `key`
            i <= arr.len()
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
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(# [trigger] arr1[k]),
{
    let mut index = 0;
    while index < arr1.len()
        invariant
            !exists|j: int| 0 <= j < index && arr2@.contains(arr1[j]),
            index <= arr1.len(),
            arr1.len() == arr1.len(), // Loop invariant for array length
            arr2.len() == arr2.len(), // Loop invariant for array length
    {
        if contains(arr2, arr1[index]) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// Score: (4, 0)
// Safe: False