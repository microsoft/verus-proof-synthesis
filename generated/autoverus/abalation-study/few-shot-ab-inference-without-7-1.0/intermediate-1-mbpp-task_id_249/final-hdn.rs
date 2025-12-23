
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
            i <= arr.len(),
            arr.len() == arr.len(), // Added invariant for array length
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
            0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && arr2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut output_arr = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|i: int, j: int|
                0 <= i < j < output_arr.len() ==> output_arr@[i] != output_arr@[j],
                0 <= k < index ==> (arr1@.contains(# [trigger] output_arr@[k]) && arr2@.contains(
                    # [trigger] output_arr@[k],
                )),
            index <= arr1.len(),
            arr1.len() == arr1.len(), // Added invariant for array length of arr1
            arr2.len() == arr2.len(), // Added invariant for array length of arr2
            output_arr.len() == output_arr.len(), // Added invariant for length of output_arr
    {
        if (contains(arr2, arr1[index]) && !contains(&output_arr, arr1[index])) {
            output_arr.push(arr1[index]);
        }
        index += 1;
    }
    output_arr
}

} // verus!

// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3