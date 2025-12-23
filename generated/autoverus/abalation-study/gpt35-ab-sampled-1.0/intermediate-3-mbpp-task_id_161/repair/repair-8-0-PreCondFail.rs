
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
            i <= str.len(),
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

/// helper function to prove the elements in output_str are from arr1 and not in arr2
proof fn elements_in_output_str(arr1: &Vec<i32>, arr2: &Vec<i32>, output_str: &Vec<i32>)
    requires
        forall |i| 0 <= i < output_str.len() ==> (
            arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])
        )
{
    assert(forall |i| 0 <= i < output_str.len() ==> (
        arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])
    ));
}

/// helper function to prove the elements in arr1 are either in arr2 or in output_str
proof fn elements_in_arr1(arr1: &Vec<i32>, arr2: &Vec<i32>, output_str: &Vec<i32>)
    requires
        forall |i| 0 <= i < arr1.len() ==> (
            arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])
        )
{
    assert(forall |i| 0 <= i < arr1.len() ==> (
        arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])
    ));
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
            index <= arr1.len(),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                elements_in_output_str(arr1, arr2, &output_str);
                elements_in_arr1(( output_str ) as &Vec<i32>, arr2, arr1);
            }
        }
        index += 1;
    }
    output_str
}

} // verus!



//             elements_in_arr1(arr1, arr2, &output_str);
// failed precondition
//         forall |i| 0 <= i < arr1.len() ==> (
//             arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])
//         )
//   failed precondition: forall |i| 0 <= i < arr1.len() ==> (             arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])         )
//   None: elements_in_arr1(arr1, arr2, &output_str)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True