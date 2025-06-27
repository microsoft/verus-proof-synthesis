
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;

    // Add the invariant as an assert right before the loop
    assert forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int| 0 <= m < i + 1 && arr[m] == key)) by {
        // No specific proof needed since array is not changed before the loop
    };

    while i < arr.len()
        invariant
            arr.len() == arr.len(), // Invariant specifying the length of the array
            forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|
                    0 <= m < i + 1 && arr[m] == key)), // Updated to cover every element of arr since arr is never changed in the loop
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
    
    // Add the invariant as an assert right before the loop
    assert forall |k:int| 0 <= k < arr1.len() ==> (arr1[k] != arr2[( index ) as int] || (exists|m: int| 0 <= m < index + 1 && arr2.contains(( arr1[m] ) as &i32))) by {
        // No specific proof needed since arrays are not changed before the loop
    };

    while index < arr1.len()
        invariant
            arr1.len() == arr1.len(), // Invariant specifying the length of arr1
            arr2.len() == arr2.len(), // Invariant specifying the length of arr2
            arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int|
                    0 <= m < index + 1 && arr2@.contains(# [trigger] arr1[m]))), // Updated to cover every element of arr1 and arr2 since they are never changed in the loop
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




//             forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|
//                     0 <= m < i + 1 && arr[m] == key)), // Updated to cover every element of arr since arr is never changed in the loop
//   None: forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|                     0 <= m < i + 1 && arr[m] == key))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True