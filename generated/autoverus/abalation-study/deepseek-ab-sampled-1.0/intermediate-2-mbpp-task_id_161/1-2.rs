
use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    invariant
        // i is within the bounds of str
        0 <= i < str.len(),
    // Additional invariant to ensure correctness
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
    invariant
        // index is within the bounds of arr1
        0 <= index < arr1.len(),
        // All elements in output_str are from arr1 and not in arr2
        output_str@.forall(|x: i32| arr1@.contains(x) && !arr2@.contains(x)),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;

        while index < arr1.len() {
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