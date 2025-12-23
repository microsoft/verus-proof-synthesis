
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
                str.len() == old(str).len(),
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
            forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(#[trigger] result[i])),
            forall|i: int|
                0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(#[trigger] arr1[i])),
    {
        let mut output_vec = Vec::new();
        let mut index: usize = 0;
        while index < arr1.len()
            invariant
                forall|j: int|
                    0 <= j < index ==> (arr2@.contains(#[trigger] arr1[j]) || output_vec@.contains(#[trigger] arr1[j])),
                forall|j: int|
                    0 <= j < output_vec.len() ==> (arr1@.contains(#[trigger] output_vec[j]) && !arr2@.contains(#[trigger] output_vec[j])),
                index <= arr1.len(),
                output_vec.len() <= index,
                arr1.len() == old(arr1).len(),
                arr2.len() == old(arr2).len(),
        {
            if !contains(arr2, arr1[index]) {
                output_vec.push(arr1[index]);
                proof {
                    assert(arr1@.contains(arr1[index]) && !arr2@.contains(arr1[index]));
                }
            }
            index += 1;
        }
        output_vec
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9geadivb`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False