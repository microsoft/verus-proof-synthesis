use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    proof {
        assert(exists|j: int|
            0 <= j < 0 && (str[j] == key) <==> (exists|k: int|
                0 <= k < str.len() && (str[k] == key))
        );
    } // Added by AI
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            exists|j: int|
                0 <= j < i && (str[j] == key) <==> (exists|k: int|
                    0 <= k < str.len() && (str[k] == key)),
            str.len() == str.len(),
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
            0 <= index <= arr1.len(),
            forall|i: int|
                0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                    # [trigger] arr1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i])
                    && !arr2@.contains(# [trigger] output_str[i])),
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // arr1 is never changed in the loop
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // arr2 is never changed in the loop
            output_str.len() <= index,
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
            output_str.len() == output_str.len(),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!

//             exists|j: int|
//                 0 <= j < i && (str[j] == key) <==> (exists|k: int|
//                     0 <= k < str.len() && (str[k] == key)),
//   None: exists|j: int|                 0 <= j < i && (str[j] == key) <==> (exists|k: int|                     0 <= k < str.len() && (str[k] == key))

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: True