
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
            arr.len() == arr.len(), // Invariant specifying the length of the array
            exists|j: int|
                0 <= j < arr.len() ==> arr[j] == key ==> (exists|k: int|
                    0 <= k < i + 1 && arr[k] == key),
            i <= arr.len(),
    {
        if (arr[i] == key) {
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
            arr1.len() == arr1.len(), // Invariant specifying the length of arr1
            arr2.len() == arr2.len(), // Invariant specifying the length of arr2
            arr2.len() <= 0 || (exists|j: int|
                0 <= j < arr1.len() && arr2@.contains(# [trigger] arr1[j]) ==> (exists|k: int|
                    0 <= k < index + 1 && arr2@.contains(# [trigger] arr1[k]))),
            index <= arr1.len(),
    {
        if (contains(arr2, arr1[index])) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
