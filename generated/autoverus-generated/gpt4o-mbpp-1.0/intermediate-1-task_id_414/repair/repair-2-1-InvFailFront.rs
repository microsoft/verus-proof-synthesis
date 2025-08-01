
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;

    assert(forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int| 0 <= m < i && arr[m] == key))); // Assert to ensure the invariant holds before entering the loop

    while i < arr.len()
        invariant
            arr.len() == arr.len(), // Invariant specifying the length of the array
            forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|
                    0 <= m < i && arr[m] == key)), // Updated to cover every element of arr since arr is never changed in the loop
            i <= arr.len(),
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;

        // Proving the invariant after incrementing i
        assert(forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int| 0 <= m < i && arr[m] == key)));
    }
    false
}

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(# [trigger] arr1[k]),
{
    let mut index = 0;

    assert(arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m])))); // Assert to ensure invariant holds before entering the loop

    while index < arr1.len()
        invariant
            arr1.len() == arr1.len(), // Invariant specifying the length of arr1
            arr2.len() == arr2.len(), // Invariant specifying the length of arr2
            arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m]))), // Updated to cover every element of arr1 and arr2 since they are never changed in the loop
            index <= arr1.len(),
    {
        if (contains(arr2, arr1[index])) {
            return true;
        }
        index += 1;

        // Proving the invariant after incrementing index
        assert(arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m]))));
    }
    false
}

} // verus!


//             forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|
//                     0 <= m < i + 1 && arr[m] == key)), // Updated to cover every element of arr since arr is never changed in the loop
//   None: forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|                     0 <= m < i + 1 && arr[m] == key))

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True