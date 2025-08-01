

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
            i <= str.len(),
            0 <= i < str.len() ==> str[i] == str@.index(i as int),
            // Ensure that the index is within bounds and reflects the array's state
            result == false ==> !exists|i: int| 0 <= i as int < str.len() && (str@.index(i as int) == key),
            // The result is false only if key is not found in the current part of the array
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
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    while index < arr1.len()
        invariant
            index <= arr1.len(),
            output_str.len() == index - count{..},
            // The length of output_str reflects the number of elements processed so far
            0 <= index < arr1.len() ==> arr1[index] == arr1@.index(index as int),
            // Each element being processed is correctly accessed from arr1
            !exists |i: int| 0 <= i < index as int < arr1.len() as int && !contains(arr2, arr1[i]),
            // Any element not contained in arr2 is added to output_str
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1