
use vstd::prelude::*;
fn main() {}
verus! {
/* ... existing lemma definitions ... */

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall |k: int| 0 <= k < i && k < str.len() ==> str[k] != key,
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
            0 <= i < result.len() ==> (arr1@.contains(result[i]) && !arr2@.contains(result[i])),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || result@.contains(arr1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])),
            forall|i: int|
                0 <= i < index ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])),
            forall|i: int|
                0 <= i < index ==> (output_str@.contains(arr1[i]) ==> !arr2@.contains(arr1[i])),
            index <= arr1.len(),
            output_str.len() <= index,
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                lemma_vec_push(output_str@, arr1[index as int], output_str.len());
            }
        }
        index += 1;
        proof {
            // Removed unnecessary lemma_vec_remove
            assert(forall|i: int| 0 <= i < index ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
        }
    }
    output_str
}

} // verus!


//             assert(forall|i: int| 0 <= i < index ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
//   assertion failed: forall|i: int| 0 <= i < index ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False