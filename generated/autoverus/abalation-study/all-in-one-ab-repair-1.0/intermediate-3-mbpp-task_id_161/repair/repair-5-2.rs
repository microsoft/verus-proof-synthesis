
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_invariant_forall]
    fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;
        while i < str.len()
            invariant
                // All elements before `i` are not equal to `key`
                forall|j: int| 0 <= j < i ==> str[j] != key,
                // `i` is within bounds of `str`
                i <= str.len(),
                // `str` length remains constant
                str.len() == old(str).len(),
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }
    
    #[verifier::loop_invariant_forall]
    fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            // each element in result is in arr1 and not in arr2
            forall|i: int| 0 <= i < result.len() ==> (arr1@.contains((#) result[i]) && !arr2@.contains((#) result[i])),
            // each element in arr1 not in arr2 is in result
            forall|i: int| 0 <= i < arr1.len() ==> (!arr2@.contains((#) arr1[i]) ==> result@.contains((#) arr1[i])),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        while index < arr1.len()
            invariant
                // Each element up to `index` in arr1 is either in arr2 or in the output_str
                forall|j: int| 0 <= j < index ==> (arr2@.contains((#) arr1[j]) || output_str@.contains((#) arr1[j])),
                // Each element in output_str is in arr1 and not in arr2
                forall|j: int| 0 <= j < output_str.len() ==> (arr1@.contains((#) output_str[j]) && !arr2@.contains((#) output_str[j])),
                // `index` is within bounds of arr1
                index <= arr1.len(),
                // The length of output_str is less than or equal to `index`
                output_str.len() <= index,
        {
            if !contains(arr2, arr1[index]) {
                output_str.push(arr1[index]);
            }
            index += 1;
        }
        output_str
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp1eloa9n9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False