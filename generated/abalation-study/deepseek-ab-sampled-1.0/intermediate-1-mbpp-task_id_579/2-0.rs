

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::vec::Vec;

fn main() {}

verus! {

    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr@.index(i) == key)),
    {
        proof {
            reveal(Seq::index);
        }
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                forall |k: int| 0 <= k < index ==> (arr@.index(k as int) != key),
            {
            if (arr@.index(index as int) == key) {
                return true;
            }
            index += 1;
        }
        false
    }

    fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < arr1.len() ==> (!contains(arr2, arr1@.index(i)) ==> result@.contains(arr1@.index(i))),
            forall|i: int|
                0 <= i < arr2.len() ==> (!contains(arr1, arr2@.index(i)) ==> result@.contains(arr2@.index(i))),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> result@.index(i as int) != result@.index(j as int),
    {
        let mut result = Vec::new();
        let mut index = 0;

        // Processing arr1
        while index < arr1.len()
            invariant
                index <= arr1.len(),
                result.len() <= arr1.len() + arr2.len(),
                forall |k: int| 0 <= k < index ==> (!contains(arr2, arr1@.index(k as int)) ==> result@.contains(arr1@.index(k as int))),
                forall |k: int| 0 <= k < result.len() ==> (!contains(arr2, result@.index(k as int)) ==> exists |m: int| m < index && arr1@.index(m as int) == result@.index(k as int)),
                // Ensure uniqueness
                forall |i: int, j: int| i < j < result.len() ==> result@.index(i as int) != result@.index(j as int),
        {
            if (!contains(arr2, arr1@.index(index as int)) && !contains(&result, arr1@.index(index as int))) {
                result.push(arr1@.index(index as int));
            }
            index += 1;
        }

        // Processing arr2
        index = 0;
        while index < arr2.len()
            invariant
                index <= arr2.len(),
                result.len() <= arr1.len() + arr2.len(),
                forall |k: int| 0 <= k < index ==> (!contains(arr1, arr2@.index(k as int)) ==> result@.contains(arr2@.index(k as int))),
                forall |k: int| 0 <= k < result.len() ==> (!contains(arr1, result@.index(k as int)) ==> exists |m: int| m < index && arr2@.index(m as int) == result@.index(k as int)),
                // Ensure uniqueness
                forall |i: int, j: int| i < j < result.len() ==> result@.index(i as int) != result@.index(j as int),
        {
            if (!contains(arr1, arr2@.index(index as int)) && !contains(&result, arr2@.index(index as int))) {
                result.push(arr2@.index(index as int));
            }
            index += 1;
        }

        result
    }
} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1