
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
                key >= i32::MIN,
                key <= i32::MAX,
                str.len() == str.len(),
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    #[verifier::loop_isolation(false)]
    fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(
                    # [trigger] result[i])),
            forall|i: int|
                0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || result@.contains(
                    # [trigger] arr1[i])),
    {
        let mut output = Vec::new();
        let mut index: usize = 0;
        while index < arr1.len()
            invariant
                forall|j: int|
                    0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output@.contains(
                        # [trigger] arr1[j])),
                forall|j: int|
                    0 <= j < output.len() ==> (arr1@.contains(# [trigger] output[j])
                        && !arr2@.contains(# [trigger] output[j])),
                index <= arr1.len(),
                output.len() <= index,
                arr1.len() >= 0,
                arr1.len() <= usize::MAX,
                arr2.len() >= 0,
                arr2.len() <= usize::MAX,
        {
            if !contains(arr2, arr1[index]) {
                output.push(arr1[index]);
            }
            index += 1;
        }
        output
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpg1wda4u4`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False