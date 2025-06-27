
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
            i <= str.len(),
            0 <= i <= str.len(),
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

/// Helper function to ensure elements in result are in arr1 and not in arr2
proof fn elements_are_in_arr1_not_in_arr2(arr1: &Vec<i32>, arr2: &Vec<i32>, result: &Vec<i32>)
    ensures
        forall |i| 0 <= i < result.len() ==> (arr1@.contains(result[i]) && !arr2@.contains(result[i])),
{
    for item in result {
        assert(arr1.contains(( *item ) as &i32) && !arr2.contains(*item));
    }
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall |i| 0 <= i < result.len() ==> (arr1@.contains(result[i]) && !arr2@.contains(result[i])),
        forall |i| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || result@.contains(arr1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall |i| 0 <= i < index ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])),
            forall |i| 0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])),
            index <= arr1.len(),
            0 <= index <= arr1.len(),
            forall |i| 0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])),
            output_str.len() == 0 || arr1@.contains(output_str[output_str.len() - 1]),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
        proof {
             elements_are_in_arr1_not_in_arr2(arr1, arr2, &output_str);
        }
    }
    output_str
}

} // verus!



//             assert(forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
//                     # [trigger] arr1[i],
//                 )));
//   assertion failed: forall|i: int| 0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(                     # [trigger] arr1[i],                 ))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False