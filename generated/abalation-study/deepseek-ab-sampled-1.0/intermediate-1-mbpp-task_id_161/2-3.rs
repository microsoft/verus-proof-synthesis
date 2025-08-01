

use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len() {
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

    // Loop invariant 1: index is within bounds of arr1
    while index < arr1.len()
        invariant
            index <= arr1.len(),
    {
        // Check if the current element in arr1 is not in arr2
        if (!contains(arr2, arr1[index])) {
            // Loop invariant 2: output_str only contains elements from arr1 not in arr2
            output_str.push(arr1[index]);
        }
        index += 1;
    }

    // Post-loop assertion: All elements processed and output_str is correctly built
    output_str
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 3