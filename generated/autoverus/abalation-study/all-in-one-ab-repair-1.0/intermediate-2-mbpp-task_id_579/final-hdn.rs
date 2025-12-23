
use vstd::prelude::*;
fn main() {}

verus! {

    // Ensure loop isolation for invariant preservation
    #[verifier::loop_isolation(false)]
    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut index = 0;
        while index < arr.len()
            invariant
                exists|k: int| 0 <= k < index ==> arr[k] != key,
                index <= arr.len(),
                arr.len() == arr.len(),   // Loop invariant specifying the length of the array
        {
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
                forall|i: int|
                    0 <= i < index ==> (!contains(arr2, arr1[i]) ==> result@.contains(arr1[i])),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> # [trigger] result[k] != # [trigger] result[l],
                index <= arr1.len(),
                arr1.len() == arr1.len(), // Loop invariant specifying the length of arr1,
                result@.len() <= arr1.len() + arr2.len(), // Providing bounds for result@
        {
            if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
                result.push(arr1[index]);
                proof {
                    assert(result@.contains(arr1[index])); // Correct assertion to compare sequences
                }
            }
            index += 1;
        }
        
        let mut index = 0;
        while index < arr2.len()
            invariant
                forall|i: int|
                    0 <= i < arr1.len() ==> (!contains(arr2, arr1[i]) ==> result@.contains(arr1[i])),
                forall|i: int|
                    0 <= i < index ==> (!contains(arr1, arr2[i]) ==> result@.contains(arr2[i])),
                forall|k: int, l: int|
                    0 <= k < l < result.len() ==> # [trigger] result[k] != # [trigger] result[l],
                index <= arr2.len(),
                arr2.len() == arr2.len(), // Loop invariant specifying the length of arr2
                result@.len() <= arr1.len() + arr2.len(), // Providing bounds for result@
        {
            if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
                result.push(arr2[index]);
                proof {
                    assert(result@.contains(arr2[index])); // Correct assertion to compare sequences
                }
            }
            index += 1;
        }
        result
    }

}


// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2