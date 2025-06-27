
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    
    // Assert the invariant before the loop starts
    assert forall|j: int| 0 <= j < str.len() ==> (str[j] == key) == (exists|k: int| 0 <= k < i && (str[k] == key)) by {
        // Initially, i = 0, so there are no k in the range 0 <= k < i
        if str.len() > 0 && str[j] == key {
            assert false; // This line is essentially saying "there is no such k", which is correct initially
        }
    };

    while i < str.len()
        invariant
            forall|j: int| 0 <= j < str.len() ==> (str[j] == key) == (exists|k: int| 0 <= k < i && (str[k] == key)),
            i <= str.len(),
            key == key, // key is a constant parameter
            str.len() == str.len(), // invariant for str
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
    while index < arr1.len()
        invariant
            forall|i: int| 0 <= i < index ==> arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(# [trigger] arr1[i]),
            forall|i: int| 0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i]) && !arr2@.contains(# [trigger] output_str[i])),
            index <= arr1.len(),
            output_str.len() <= arr1.len(),
            arr1.len() == arr1.len(), // arr1 is a constant parameter
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // arr2 is a constant parameter
            output_str.len() == output_str.len(), // invariant for output_str
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


//             forall|j: int| 0 <= j < str.len() ==> (str[j] == key) == (exists|k: int| 0 <= k < i && (str[k] == key)), // Modified to cover every element
//   None: forall|j: int| 0 <= j < str.len() ==> (str[j] == key) == (exists|k: int| 0 <= k < i && (str[k] == key))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False