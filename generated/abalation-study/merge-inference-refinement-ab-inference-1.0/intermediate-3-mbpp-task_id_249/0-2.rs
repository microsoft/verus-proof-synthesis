use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            arr.len() == old(arr).len(), // length constraint invariant
            // the key should exist in array in previous iterations
            exists|x: int| 0 <= x < i ==> arr[x] == key ==>(result==true)
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && arr2@.contains(#[trigger] result[i])),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut output_arr = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            index <= arr1.len(),
            output_arr.len() <= arr1.len(),
            arr1.len() == old(arr1).len(), // maintaining previous state of persisted array
            arr2.len() == old(arr2).len(), // maintaining previous state of persisted array
            forall |i: int|
                0 <= i < output_arr.len() ==> (arr1@.contains(#[trigger] output_arr[i]) && arr2@.contains(#[trigger] output_arr[i])), // element must be common
            forall |i: int, j: int| 
                0 <= i < j < output_arr.len() ==> output_arr[i] != output_arr[j] // no duplicates allowed
            {
            
        if (contains(arr2, arr1[index]) && !contains(&output_arr, arr1[index])) {
            output_arr.push(arr1[index]);
        }
        index += 1;
    }
    output_arr
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1