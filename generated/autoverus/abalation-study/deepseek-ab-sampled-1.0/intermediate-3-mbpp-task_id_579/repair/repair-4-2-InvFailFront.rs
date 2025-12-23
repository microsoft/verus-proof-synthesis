

use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    requires
        sorted_between(arr@, 0, arr.len() as int),
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len() 
        invariant
            index <= arr.len(),
            sorted_between(arr@, 0, arr.len() as int),
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        sorted_between(arr1@, 0, arr1.len() as int),
        sorted_between(arr2@, 0, arr2.len() as int),
    ensures
        sorted_between(result@, 0, result.len() as int),
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while (index < arr1.len())
        invariant
            index <= arr1.len(),
            result.len() <= index + arr2.len(),
            sorted_between(result@, 0, result.len() as int),
            forall|i: int| 0 <= i < index ==> 
                 (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(arr1[i])),
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    proof {
        assert(result.len() <= arr1.len());
    }
    while (index < arr2.len())
        invariant
            index <= arr2.len(),
            result.len() <= arr1.len() + index,
            sorted_between(result@, 0, result.len() as int),
            forall|i: int| 0 <= i < index ==> 
                 (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(arr2[i])),
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!

//             result.len() <= arr1.len() + index,
//   None: result.len() <= arr1.len() + index

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False