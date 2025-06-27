
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
            0 <= i < str.len() || i == str.len(),
            i <= str.len(),
            str.len() >= 0,
            str.len() == str@.len(),
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
            forall|j: int|
                0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(
                    # [trigger] arr1[j],
                )),
            forall|j: int|
                0 <= j < output_str.len() ==> (arr1@.contains(# [trigger] output_str[j])
                    && !arr2@.contains(# [trigger] output_str[j])),
            index <= arr1.len(),
            output_str.len() <= arr1.len(),
            arr1.len() == arr1@.len(),
            arr2.len() == arr2@.len(),
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
            proof {
                lemma_output_str_len_invariant(arr1, &output_str);
                assert(output_str.len() <= arr1.len());
            }
        }
        index += 1;
        proof {
            lemma_output_str_len_invariant(arr1, &output_str);
            assert(output_str.len() <= arr1.len());
        }
    }
    output_str
}

proof fn lemma_output_str_len_invariant(arr1: &Vec<i32>, output_str: &Vec<i32>) {
    ensures
        output_str.len() <= arr1.len(),
    {
        assert(output_str.len() <= arr1.len());
    }
}

} // verus!


//                 assert(output_str.len() <= arr1.len());
//   assertion failed: output_str.len() <= arr1.len()

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False