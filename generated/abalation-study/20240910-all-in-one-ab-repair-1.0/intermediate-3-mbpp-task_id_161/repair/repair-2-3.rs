
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
        result.len() <= arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(result[i]) && !arr2@.contains(result[i])),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || result@.contains(arr1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall|j: int|
                0 <= j < index ==> (arr2@.contains(arr1[j]) || output_str@.contains(arr1[j])),
            forall|j: int|
                0 <= j < output_str.len() ==> (arr1@.contains(output_str[j]) && !arr2@.contains(output_str[j])),
            index <= arr1.len(),
            output_str.len() <= index,
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7jkeho0t`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False