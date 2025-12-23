
use vstd::prelude::*;

#[verifier::ensures]
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || result@.contains(
                # [trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|i: int|
                0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                    # [trigger] arr1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i])
                    && !arr2@.contains(# [trigger] output_str[i])),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i])
                    && !arr2@.contains(# [trigger] output_str[i])),
            index <= arr1.len(),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                lemma_vec_push(output_str@, arr1[index], output_str.len() - 1);
            }
        }
        index += 1;
    }
    output_str
}


//             assert(forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
//   assertion failed: forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False