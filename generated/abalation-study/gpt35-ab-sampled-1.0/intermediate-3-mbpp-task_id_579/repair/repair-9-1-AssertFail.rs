
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

    /// helper function to prove that result contains elements from arr1 that are not present in arr2
    proof fn arr1_not_in_arr2_in_result(arr1: &Vec<i32>, arr2: &Vec<i32>, result: &Vec<i32>)
        ensures
            forall |i| 0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(arr1[i])),
        decreases arr1.len()
    {
        let mut index = 0;
        while index < arr1.len()
            invariant
                0 <= index <= arr1.len(),
                forall |i| 0 <= i < index ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(arr1[i])),
        {
            if (!contains(arr2, arr1[index]) && !contains(result, arr1[index])) {
                assert(forall |i| 0 <= i < index ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(arr1[i])));
                result.push(arr1[index]);
            }
            index += 1;
        }
    }

    /// helper function to prove that result contains elements from arr2 that are not present in arr1
    proof fn arr2_not_in_arr1_in_result(arr1: &Vec<i32>, arr2: &Vec<i32>, result: &Vec<i32>)
        ensures
            forall |i| 0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i])),
        decreases arr2.len()
    {
        let mut index = 0;
        while index < arr2.len()
            invariant
                0 <= index <= arr2.len(),
                forall |i| 0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i])),
        {
            if (!contains(arr1, arr2[index]) && !contains(result, arr2[index])) {
                assert(forall |i| 0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i])));
                result.push(arr2[index]);
            }
            index += 1;
        }
    }

    fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall |i| 0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(arr1[i])),
            forall |i| 0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i])),
            forall |i, j| 0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
    {
        let mut result = Vec::new();

        arr1_not_in_arr2_in_result(arr1, arr2, &result);
        arr2_not_in_arr1_in_result(arr1, arr2, &result);

        result
    }
} // verus!


//                 assert(forall|i: int| 0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i])));
//   assertion failed: forall|i: int| 0 <= i < index ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False