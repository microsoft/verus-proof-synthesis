
use vstd::prelude::*;
fn main() {}

verus! {
#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    assert forall |k: int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int| 0 <= m < 0 + 1 && arr[m] == key))
        by {
            assert(false); // if k < arr.len() and arr[k] == key, 0 <= k < 0 cannot be true.
        };
    
    let mut i = 0;
    while i < arr.len()
        invariant
            arr.len() == arr.len(), // Invariant specifying the length of the array
            forall |k: int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int| 0 <= m < i + 1 && arr[m] == key)), 
            i <= arr.len(),
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
    assert forall |k: int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < 0 + 1 && arr2@.contains(# [trigger] arr1[m])))
        by {
            assert(false); // if k < arr1.len() and arr2.contains(arr1[k]), 0 <= k < 0 cannot be true.
        };
    
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr1.len(), // Invariant specifying the length of arr1
            arr2.len() == arr2.len(), // Invariant specifying the length of arr2
            arr2.len() <= 0 || forall |k: int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index + 1 && arr2@.contains(# [trigger] arr1[m]))), // 
            index <= arr1.len(),
    {
        if contains(arr2, arr1[index]) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!


//             forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|
//                     0 <= m < i + 1 && arr[m] == key)), // Updated to cover every element of arr since arr is never changed in the loop
//   None: forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|                     0 <= m < i + 1 && arr[m] == key))

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: False