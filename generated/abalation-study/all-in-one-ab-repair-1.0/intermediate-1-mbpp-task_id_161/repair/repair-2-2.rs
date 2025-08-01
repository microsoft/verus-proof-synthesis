
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
                // Specify the length of the array
                str.len() == str.len(),
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
            forall|i: int| 0 <= i < result.len() ==> (exists|j: int| 0 <= j < arr1.len() && (result[i] == arr1[j]) && !arr2.contains(result[i])),
            forall|i: int| 0 <= i < arr1.len() ==> (arr2.contains(arr1[i]) || result.contains(arr1[i])),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        while index < arr1.len()
            invariant
                forall|j: int| 0 <= j < index ==> (arr2.contains(arr1[j]) || output_str.contains(arr1[j])),
                forall|j: int| 0 <= j < output_str.len() ==> (arr1.contains(output_str[j]) && !arr2.contains(output_str[j])),
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
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_v7jzkqg`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False