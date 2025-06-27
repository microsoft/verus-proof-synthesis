
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    #[verifier::proof(fn)]
    proof fn contains(arr: &Seq<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists |i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut index = 0;
        while index < arr.len()
            invariant
                exists |k: int| 0 <= k < index ==> arr[k] != key,
                index <= arr.len(),
        {
            if arr[index] == key {
                return true;
            }
            index += 1;
        }
        result = false;
    }

    #[verifier::proof(fn)]
    proof fn find_dissimilar(arr1: &Seq<i32>, arr2: &Seq<i32>) -> (result: Seq<i32>)
        ensures
            forall |i: int| 0 <= i < arr1.len() ==> (!arr2.contains(&(arr1[i])) ==> result.contains(&(arr1[i]))),
            forall |i: int| 0 <= i < arr2.len() ==> (!arr1.contains(&(arr2[i])) ==> result.contains(&(arr2[i]))),
            forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    {
        let mut result = Seq::empty();

        let mut index = 0;
        while index < arr1.len()
            invariant
                forall |i: int| 0 <= i < index ==> (!arr2.contains(&(arr1[i])) ==> result.contains(&(arr1[i]))),
                forall |k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr1.len(),
        {
            if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
                result = result.push(arr1[index]);
            }
            index += 1;
        }

        index = 0;
        while index < arr2.len()
            invariant
                forall |i: int| 0 <= i < arr1.len() ==> (!arr2.contains(&(arr1[i])) ==> result.contains(&(arr1[i]))),
                forall |i: int| 0 <= i < index ==> (!arr1.contains(&(arr2[i])) ==> result.contains(&(arr2[i]))),
                forall |k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
                index <= arr2.len(),
        {
            if !contains(arr1, arr2[index]) && !contains(&result, arr2[index]) {
                result = result.push(arr2[index]);
            }
            index += 1;
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprmk2tg3c`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False