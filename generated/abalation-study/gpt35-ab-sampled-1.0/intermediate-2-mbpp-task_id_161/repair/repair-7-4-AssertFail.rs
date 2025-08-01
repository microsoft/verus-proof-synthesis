
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
            0 <= i <= str.len(),
            forall|j: int| 0 <= j < i ==> str[j] != key,
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn lemma_existing_element_in_original_array(arr1: &Vec<i32>, index: int, output_str: &Vec<i32>, arr2: &Vec<i32>)
    ensures forall|j: int| 0 <= j < index + 1 ==> (!arr2@.contains(arr1[j]) ==> output_str@.contains(arr1[j]))
{
    // proof for the existing elements in the original array also exist in the output array
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(result[i]) && !arr2@.contains(result[i])),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || result@.contains(arr1[i]))
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|j: int|
                0 <= j < index ==> (!arr2@.contains(arr1[j]) ==> output_str@.contains(arr1[j]))
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                lemma_existing_element_in_original_array(arr1, ( index ) as int, &output_str, arr2);
            }
        }
        index += 1;
    }
    output_str
}

} // verus!



//                 assert(forall|j: int| 0 <= j < index + 1 ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(
//                     # [trigger] arr1[j],
//                 )));
//   assertion failed: forall|j: int| 0 <= j < index + 1 ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(                     # [trigger] arr1[j],                 ))

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: False