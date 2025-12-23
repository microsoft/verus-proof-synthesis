
use vstd::prelude::*;
fn main() {}

verus! {

spec fn contains(arr: Seq<i32>, key: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr.index(i) == key
}

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
        if arr[index] == key {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!contains(arr2@, arr1[i]) ==> result@.contains(arr1[i])),
        forall|i: int|
            0 <= i < arr2.len() ==> (!contains(arr1@, arr2[i]) ==> result@.contains(arr2[i])),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    
    while index < arr1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (!contains(arr2@, arr1[i]) ==> result@.contains(arr1[i])),
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> result[k] != result[l],
            index <= arr1.len(),
            arr1.len() == arr1.len(), // Loop invariant specifying the length of arr1
            result@ == result@, // Loop invariant specifying the invariant nature of result
    {
        if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
            result.push(arr1[index]);
            proof {
                assert(result@ == old(result@).push(arr1[index])); 
            }
        }
        index += 1;
    }
    
    index = 0; // reusing the same variable "index", reinitialize it
    while index < arr2.len()
        invariant
            forall|i: int|
                0 <= i < arr1.len() ==> (!contains(arr2@, arr1[i]) ==> result@.contains(arr1[i])),
            forall|i: int|
                0 <= i < index ==> (!contains(array1@, array2[i]) ==> result@.contains(array2[i])),
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> result[k] != result[l],
            index <= arr2.len(),
            arr2.len() == arr2.len(), // Loop invariant specifying the length of arr2
            result@ == result@, // Loop invariant specifying the invariant nature of result
    {
        if !contains(arr1, arr2[index]) && !contains(&result, arr2[index]) {
            result.push(arr2[index]);
            proof {
                assert(result@ == old(result@).push(arr2[index]));
            }
        }
        index += 1;
    }

    result
}

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp0pzmwc8m`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False