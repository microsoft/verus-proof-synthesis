
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
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
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        // The result only contains elements from arr1 that are not in arr2
        forall|i: int| 0 <= i < result.len() ==> (arr1@.contains(result[i]) && !arr2@.contains(result[i])),
        // Every element in arr1 is either in arr2 or in result
        forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || result@.contains(arr1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall|j: int| 0 <= j < index ==> (arr2@.contains(arr1[j]) || output_str@.contains(arr1[j])),
            forall|j: int| 0 <= j < output_str.len() ==> (arr1@.contains(output_str[j]) && !arr2@.contains(output_str[j])),
            index <= arr1.len(),
            output_str.len() <= arr1.len(), // Ensures output_str is within expected bounds
    {
        if !contains(arr2, arr1[index]) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpar27vn4p`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False