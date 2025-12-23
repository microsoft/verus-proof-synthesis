use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    proof {
        assert(!exists|j: int| 0 <= j < i && (arr[j] == key));
    }
    while i < arr.len()
        invariant
            !exists|j: int| 0 <= j < i && (arr[j] == key), // Invariant fixed to correctly express the property
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
            forall|k: int| 0 <= k < index ==> arr2@.contains(# [trigger] arr1[k]), // Invariant modified to cover every element because `arr1` is not modified in this loop
            index <= arr1.len(),
    {
        if (contains(arr2, arr1[index])) {
            return true;
        }
        index += 1;
        proof {
            assert(forall|k: int| 0 <= k < index ==> arr2@.contains(# arr1[k]));
        } // Added by AI
    }
    false
}

} // verus!

//             forall|k: int| 0 <= k < index ==> arr2@.contains(# [trigger] arr1[k]), // Invariant modified to cover every element because `arr1` is not modified in this loop
//   None: forall|k: int| 0 <= k < index ==> arr2@.contains(# [trigger] arr1[k])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False