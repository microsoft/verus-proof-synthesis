
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
            i <= str.len(), // index does not exceed the vector length
            for (j in 0 to i) {
                // Before this iteration, none of the elements from 0 to i-1 were equal to key
                assert!(str[j] != key);
            }
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
            index <= arr1.len(), // index does not exceed the vector length
            // All elements in output_str up to now are correctly chosen (not in arr2)
            for (j in 0 to index) {
                if (!contains(arr2, arr1[j])) {
                    assert!(output_str.contains(arr1[j]));
                }
            }
        {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1