

use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool) {
    #[ghost]
    let g = array::Array::new(arr.len(), 0);
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= arr.len(),
    {
        g[index] = arr[index];
        index += 1;
    }
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= arr.len(),
    {
        if (g[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(arr1[i])),
        forall|i: int| 0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i])),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    let ghost g_arr1 = array::Array::new(arr1.len(), 0);
    let ghost g_arr2 = array::Array::new(arr2.len(), 0);
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            0 <= arr1.len(),
            result.len() <= index,
            forall|g: usize, h: usize| g < h < result.len() ==> result[g] != result[h],
        ghost_invariant
            (g_arr1 == result@.map(|x| x)),
    {
        g_arr1[index] = arr1[index];
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    while index < arr2.len()
        invariant
            0 <= index <= arr2.len(),
            0 <= arr2.len(),
            result.len() <= index + arr1.len(),
            forall|g: usize, h: usize| g < h < result.len() ==> result[g] != result[h],
        ghost_invariant
            (g_arr2 == result@.map(|x| x)),
    {
        g_arr2[index] = arr2[index];
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}
}

// failed this postcondition
//         forall|i: int|
//             0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
//                 arr2[i],
//             )),
// at the end of the function body
// {
//     let mut result = Vec::new();
//     let mut index = 0;
//     while index < arr1.len()
// ...
//     result
// }
//   at the end of the function body: {     let mut result = Vec::new();     let mut index = 0;     while index < arr1.len()         invariant             0 <= index <= arr1.len(),             0 <= arr1.len(),             result.len() <= index,             forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],     {         if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {             result.push(arr1[index]);         }         index += 1;     }     let mut index = 0;     while index < arr2.len()         invariant             0 <= index <= arr2.len(),             0 <= arr2.len(),             result.len() <= index + arr1.len(),             forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],     {         if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {             result.push(arr2[index]);         }         index += 1;     }     result }
//   failed this postcondition: forall|i: int|             0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(                 arr2[i],             ))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False