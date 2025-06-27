
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn contains(arr: Seq<i32>, key: i32) -> bool {
        exists |i: int| 0 <= i < arr.len() && arr[i] == key
    }

    // Implementing a function to push an element to a sequence
    proof fn push(seq: Seq<i32>, elem: i32) -> (new_seq: Seq<i32>)
        ensures
            new_seq.len() == seq.len() + 1,
            forall |i: int| 0 <= i < seq.len() ==> new_seq[i] == seq[i],
            new_seq[seq.len()] == elem,
    {
        seq.push(elem)
    }

    fn test_contains(arr: &Vec<i32>, key: i32) -> bool {
        let arr_seq = arr@;
        contains(arr_seq, key)
    }

    fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall |i: int| 0 <= i < arr1.len() ==> (!contains(arr2@, arr1[i]) ==> (contains(result@, arr1[i]))),
            forall |i: int| 0 <= i < arr2.len() ==> (!contains(arr1@, arr2[i]) ==> (contains(result@, arr2[i]))),
            forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    {
        let mut result: Vec<i32> = Vec::new();

        // Processing the first array
        for i in 0..arr1.len()
            invariant
                forall |k: int| 0 <= k < i ==> (!contains(arr2@, arr1[k]) ==> (contains(result@, arr1[k]))),
                arr1.len() == arr1.len(),
                result@.len() <= arr1.len() + arr2.len(),
                forall |k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
        {
            let key = arr1[i];
            if !test_contains(arr2, key) && !test_contains(&result, key) {
                result.push(key);
            }
        }

        // Processing the second array
        for i in 0..arr2.len()
            invariant
                forall |k: int| 0 <= k < arr1.len() ==> (!contains(arr2@, arr1[k]) ==> (contains(result@, arr1[k]))),
                forall |k: int| 0 <= k < i ==> (!contains(arr1@, arr2[k]) ==> (contains(result@, arr2[k]))),
                arr2.len() == arr2.len(),
                result@.len() <= arr1.len() + arr2.len(),
                forall |k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
        {
            let key = arr2[i];
            if !test_contains(arr1, key) && !test_contains(&result, key) {
                result.push(key);
            }
        }

        result
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4ht3eg9o`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False