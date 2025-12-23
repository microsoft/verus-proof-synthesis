

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
            // Invariants for the loop
            0 <= i <= str.len(),
            i <= str.len() - 1,
            // At each step, we've checked that none of the previously considered elements are equal to `key`
            forall |k: int| 0 <= k < i ==> str[k] != key,
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
            // Invariants for the loop
            0 <= index <= arr1.len(),
            index <= arr1.len() - 1,
            // // For all elements in `output_str` so far:
            // forall |k: int| 0 <= k < output_str.len() ==> arr1@.contains(output_str[k]) && !arr2@.contains(output_str[k]),
            // // For all elements in arr1 that are before `index`:
            // forall |k: int| 0 <= k < index ==> (arr2@.contains(arr1@.index(k)) || output_str@.contains(arr1@.index(k))),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 4, Verus Errors: 4