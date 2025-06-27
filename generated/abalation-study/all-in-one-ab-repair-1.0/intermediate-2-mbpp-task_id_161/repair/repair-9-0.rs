
use vstd::prelude::*;
fn main() {}

verus! {

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),
    {
        if str[i] == key {
            return true;
        }
        i += 1;
        proof {
            // Ensuring that the invariant still holds after incrementing `i`
            assert(forall|j: int| 0 <= j < i ==> str[j] != key);
        }
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        // Result elements are from `arr1` and not in `arr2`
        forall|i: int| 0 <= i < result.len() ==> arr1@.contains(#[trigger] result[i]) && !arr2@.contains(#[trigger] result[i]),
        // All elements in `arr1` are in `arr2` or `result`
        forall|i: int| 0 <= i < arr1.len() ==> arr2@.contains(#[trigger] arr1[i]) || result@.contains(#[trigger] arr1[i]),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            // All previously checked elements in `arr1` either belong to `arr2` or are in `output_str`
            forall|j: int| 0 <= j < index ==> arr2@.contains(#[trigger] arr1[j]) || output_str@.contains(#[trigger] arr1[j]),
            // All elements in `output_str` are from `arr1` and not in `arr2`
            forall|j: int| 0 <= j < output_str.len() ==> arr1@.contains(#[trigger] output_str[j]) && !arr2@.contains(#[trigger] output_str[j]),
            index <= arr1.len(),
            output_str.len() <= arr1.len(), // Ensures output_str is within expected bounds
    {
        if !contains(arr2, arr1[index]) {
            output_str.push(arr1[index]);
        }
        index += 1;
        proof {
            // Reassert invariants to ensure they hold true after the loop body’s execution
            assert(forall|j: int| 0 <= j < index ==> arr2@.contains(#[trigger] arr1[j]) || output_str@.contains(#[trigger] arr1[j]));
            assert(forall|j: int| 0 <= j < output_str.len() ==> arr1@.contains(#[trigger] output_str[j]) && !arr2@.contains(#[trigger] output_str[j]));
        }
    }
    output_str
}

}



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprcpxz76l`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2
// Safe: False