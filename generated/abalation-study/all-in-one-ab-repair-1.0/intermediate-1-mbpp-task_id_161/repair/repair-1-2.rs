
forall|j: int|
    0 <= j < index ==>
        (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j])),
forall|j: int|
    0 <= j < output_str.len() ==>
        (arr1@.contains(# [trigger] output_str[j]) && !arr2@.contains(# [trigger] output_str[j])),

In hind's sight attempting to remove elements that are present in `arr2` while preserving order in `output_str`. The antecedents in the loop invariant are having verification issues due to how they check for the contents of `output_str` relative to `arr1` and `arr2`.

The first invariant should really be conjunctively addressing those in `output_str` and not increment `index`.

We can combine the predicates into the loop invariant to correctly track indices and lengths:

rust
use vstd::prelude::*;
fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < arr.len() && arr[i] == key),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
            i <= arr.len(),
            // Add upper and lower bound invariants for key
            key >= i32::MIN,
            key <= i32::MAX,
            // Specify the length of the array
            arr.len() == arr.len(),
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(# [trigger] result[i])),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || result@.contains(# [trigger] arr1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall|j: int|
                0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j])),
            forall|j: int|
                0 <= j < output_str.len() ==> (arr1@.contains(# [trigger] output_str[j]) && !arr2@.contains(# [trigger] output_str[j])),
            index <= arr1.len(),
            output_str.len() <= index,
            // Add upper and lower bound invariants for arr1 and arr2
            arr1.len() >= 0,
            arr1.len() <= usize::MAX,
            arr2.len() >= 0,
            arr2.len() <= usize::MAX,
            // Specify the length of the arrays
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
    {
        if !contains(arr2, arr1[index]) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpk1wzifij`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 16
// Safe: False