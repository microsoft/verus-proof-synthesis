
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

/// Helper function to prove the output vector only contains elements from arr1 not in arr2
/// and no other elements
proof fn output_contains_only_arr1_not_in_arr2(arr1: &Vec<i32>, arr2: &Vec<i32>, output_str: &Vec<i32>, index: usize)
    ensures forall|j: int| 0 <= j < index + 1 ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(
        # [trigger] arr1[j],
    ))
{
    // Proof of the assertion
    assert(forall|j: int| 0 <= j < index + 1 ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(
        # [trigger] arr1[j],
    )));
}

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
        // Invariant with explanation for unchanged array
        invariant
            0 <= index <= arr1.len(),
            forall|j: int|
                0 <= j < index ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(
                    # [trigger] arr1[j],
                )),
            // Explanation: Array arr1 is not modified in this loop, as there are no calls to arr1.set() or any function that modifies arr1 elements.
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof{
                // Assertion proof using the helper function
                output_contains_only_arr1_not_in_arr2(arr1, arr2, &output_str, index);
            } // Added by AI
        }
        index += 1;
    }
    
    proof {
        // Prove the post-condition at the end of the function
        forall|i: int|
            0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i]) && !arr2@.contains(
                # [trigger] output_str[i],
            ));
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                # [trigger] arr1[i],
            ));
    }
    output_str
}

} // verus!


// failed this postcondition
//         forall|i: int|
//             0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(
//                 # [trigger] result[i],
//             )),
// at the end of the function body
// {
//     let mut output_str = Vec::new();
//     let mut index: usize = 0;
//     while index < arr1.len()
// ...
//     output_str
// }
//   at the end of the function body: {     let mut output_str = Vec::new();     let mut index: usize = 0;     while index < arr1.len()         // Invariant with explanation for unchanged array         invariant             0 <= index <= arr1.len(),             forall|j: int|                 0 <= j < index ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(                     # [trigger] arr1[j],                 )),             // Explanation: Array arr1 is not modified in this loop, as there are no calls to arr1.set() or any function that modifies arr1 elements.     {         if (!contains(arr2, arr1[index])) {             output_str.push(arr1[index]);             proof{                 // Assertion proof using the helper function                 output_contains_only_arr1_not_in_arr2(arr1, arr2, &output_str, index);             } // Added by AI         }         index += 1;     }          output_str }
//   failed this postcondition: forall|i: int|             0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(                 # [trigger] result[i],             ))

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True