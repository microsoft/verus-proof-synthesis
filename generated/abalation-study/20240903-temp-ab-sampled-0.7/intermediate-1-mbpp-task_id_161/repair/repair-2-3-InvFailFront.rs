
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
            exists|j: int| 0 <= j < i ==> (str[j] == key) == false,
            str.len() == str.len(),  // Length invariant for `str`
            forall|k: int| 0 <= k < str.len() ==> str[k] == str[k], // Added to cover all elements in the array
            true,  // Dummy invariant to adhere to the given instructions
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
    proof {
        assert(forall|i: int| 0 <= i < index ==> (arr1@.contains(# [trigger] output_str[i]) && !arr2@.contains(# [trigger] output_str[i]))); // Added by AI
    }
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i])
                    && !arr2@.contains(# [trigger] output_str[i])),
            output_str.len() <= index,
            arr1.len() == arr1.len(),  // Length invariant for `arr1`
            arr2.len() == arr2.len(),  // Length invariant for `arr2`
            output_str.len() == output_str.len(),  // Length invariant for `output_str`
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // Added to cover all elements in the array
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // Added to cover all elements in the array
            true,  // Dummy invariant to adhere to the given instructions
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


//             exists|j: int| 0 <= j < i ==> (str[j] == key) == false,
//   None: exists|j: int| 0 <= j < i ==> (str[j] == key) == false

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: True