

To fix the failed post-condition, we need to ensure that all elements in the result vector are unique. We achieve this by adding a proof block that asserts the uniqueness condition of the result vector at the end of the function.

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len() {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            index <= arr1.len(),
            forall |k: int| 0 <= k < result.len() ==> result[k] == # [trigger] result[k],
            result@.len() <= index,
            arr2@.len() == arr2.len(),
            arr1@.len() == arr1.len(),
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
        proof {
            assert(result@.len() <= index);
        }
    }
    // Now handle arr2
    let mut index = 0;
    while index < arr2.len()
        invariant
            index <= arr2.len(),
            forall |k: int| 0 <= k < result.len() ==> result[k] == # [trigger] result[k],
            result@.len() <= arr1.len() + index,
            arr2@.len() == arr2.len(),
            arr1@.len() == arr1.len(),
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
        proof {
            assert(result@.len() <= arr1.len() + index);
        }
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]);
    }
    result
}

}

// failed this postcondition
//         forall|i: int, j: int|
//             0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
// at the end of the function body
// {
//     let mut result = Vec::new();
//     let mut index = 0;
//     while index < arr1.len()
// ...
//     result
// }
//   at the end of the function body: {     let mut result = Vec::new();     let mut index = 0;     while index < arr1.len()         invariant             index <= arr1.len(),             forall |k: int| 0 <= k < result.len() ==> result[k] == # [trigger] result[k],             result@.len() <= index,             arr2@.len() == arr2.len(),             arr1@.len() == arr1.len(),     {         if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {             result.push(arr1[index]);         }         index += 1;         proof {             assert(result@.len() <= index);         }     }     // Now handle arr2     let mut index = 0;     while index < arr2.len()         invariant             index <= arr2.len(),             forall |k: int| 0 <= k < result.len() ==> result[k] == # [trigger] result[k],             result@.len() <= arr1.len() + index,             arr2@.len() == arr2.len(),             arr1@.len() == arr1.len(),     {         if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {             result.push(arr2[index]);         }         index += 1;         proof {             assert(result@.len() <= arr1.len() + index);         }     }     result }
//   failed this postcondition: forall|i: int, j: int|             0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False