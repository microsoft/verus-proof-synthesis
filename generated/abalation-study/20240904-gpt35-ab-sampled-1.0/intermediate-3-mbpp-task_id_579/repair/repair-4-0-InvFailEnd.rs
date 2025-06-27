
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]

    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut index = 0;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
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
                0 <= index <= arr1.len(),
                forall|i: int|
                    0 <= i < index ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                        arr1[i],
                    )),
                forall|i: int, j: int|
                    0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
        {
            if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
                result.push(arr1[index]);
            }
            index += 1;
        }
        let mut index2 = 0; // Variable name changed to index2
        while index2 < arr2.len() // Variable name changed to index2
            invariant
                0 <= index2 <= arr2.len(),
                forall|i: int, j: int|
                    0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
                forall|i: int|
                    0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                        arr1[i],
                    )),
                forall|i: int|
                    0 <= i < index2 ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
                        arr2[i],
                    )),
        {
            if (!contains(arr1, arr2[index2]) && !contains(&result, arr2[index2])) {
                result.push(arr2[index2]);
            }
            index2 += 1; // Variable name changed to index2
        }
        result
    }
} // verus!


//                 forall|i: int|
//                     0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
//                         arr2[i],
//                     )),
//   None: forall|i: int|                     0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(                         arr2[i],                     ))

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: False