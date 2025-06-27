
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
                // Add upper and lower bound invariants for key
                key >= i32::MIN,
                key <= i32::MAX,
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int| 0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(#[trigger] result[i])),
            forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(#[trigger] arr1[i])),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        while index < arr1.len()
            invariant
                forall|j: int| 0 <= j < index ==> (arr2@.contains(#[trigger] arr1[j]) || output_str@.contains(#[trigger] arr1[j])),
                forall|j: int| 0 <= j < output_str.len() ==> (arr1@.contains(#[trigger] output_str[j]) && !arr2@.contains(#[trigger] output_str[j])),
                index <= arr1.len(),
                output_str.len() <= index,
                // Adding necessary length checks
                arr1.len() == arr1.len(),
                arr2.len() == arr2.len(),
        {
            if !contains(arr2, arr1[index]) {
                output_str.push(arr1[index]);
                proof {
                    let len = output_str.len();
                    assert(arr1@.contains(#[trigger] output_str[len - 1]) && !arr2@.contains(#[trigger] output_str[len-1]));
                }
            }
            index += 1;
            proof {
                assert(forall|j: int| 0 <= j < index ==> (arr2@.contains(#[trigger] arr1[j]) || output_str@.contains(#[trigger] arr1[j])));
                assert(forall|j: int| 0 <= j < output_str.len() ==> (arr1@.contains(#[trigger] output_str[j]) && !arr2@.contains(#[trigger] output_str[j])));
            }
        }
        output_str
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp40jvszoo`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False