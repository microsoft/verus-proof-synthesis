
use vstd::prelude::*;
fn main() {}
verus! {

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
            forall|i: int|
                0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                    # [trigger] arr1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i])
                    && !arr2@.contains(# [trigger] output_str[i])),
            index <= arr1.len(),
            0 <= index <= arr1.len(),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i])
                    && !arr2@.contains(# [trigger] output_str[i])),
            output_str.len() == 0 || arr1@.contains(# [trigger] output_str[output_str.len() - 1]),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                lemma_vec_push(output_str, arr1[index], output_str.len() as usize);
                assert(forall|i: int| 0 <= i < index + 1 ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                        # [trigger] arr1[i],
                    )));
            }
        }
        index += 1;
    }
    output_str
}

} // verus!


//             assert(forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
//                     # [trigger] arr1[i],
//                 )));
//   assertion failed: forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(                     # [trigger] arr1[i],                 ))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False