
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

proof fn arr2_not_contains_output_str_elements(arr1: &Seq<i32>, arr2: &Seq<i32>, output_str: &Seq<i32>, index: usize)
    requires
        forall |j: int| 0 <= j < index ==> (!arr2@.contains(arr1[j]) ==> output_str@.contains(arr1[j])),
{
    if index > 0 {
        arr2_not_contains_output_str_elements(arr1, arr2, output_str, ( index - 1 ) as usize);
    }
    if !arr2@.contains(arr1[index]) {
        assert(forall |j: int| 0 <= j < index + 1 ==> (!arr2@.contains(arr1[j]) ==> output_str@.contains(arr1[j])));
    }
}

fn remove_elements(arr1: &Seq<i32>, arr2: &Seq<i32>) -> (result: Seq<i32>)
    requires
        arr1.len() <= 0x1_0000_0000,
        arr2.len() <= 0x1_0000_0000,
    ensures
        forall |i: int| 0 <= i < result.len() ==> (arr1@.contains(result[i]) && !arr2@.contains(result[i])),
        forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || result@.contains(arr1[i])),
{
    let mut output_str = Seq::empty();
    let mut index: usize = 0;
    while index < arr1.len()
        // Invariant with explanation for unchanged array
        invariant
            0 <= index <= arr1.len(),
            arr2_not_contains_output_str_elements(arr1, arr2, &output_str, index),
            // Explanation: Array arr1 is not modified in this loop, as there are no calls to arr1.set() or any function that modifies arr1 elements.
    {
        if (!contains(arr2.to_vec(), arr1.index(index))) {
            output_str = output_str.push(arr1.index(index));
        }
        arr2_not_contains_output_str_elements(arr1, arr2, &output_str, index);
        index += 1;
    }
    output_str
}

} // verus!



//                 assert(forall|j: int| 0 <= j < index + 1 ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(
//                     # [trigger] arr1[j],
//                 )));
//   assertion failed: forall|j: int| 0 <= j < index + 1 ==> (!arr2@.contains(# [trigger] arr1[j]) ==> output_str@.contains(                     # [trigger] arr1[j],                 ))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 15
// Safe: False