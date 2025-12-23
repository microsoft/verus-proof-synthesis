
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
                forall|j: int| 0 <= j < i ==> str[j] != key,
                i <= str.len(),
                str.len() == str.len(),
        {
            if str[i] == key {
                proof {
                    assert(str[i] == key);
                    assert(exists|j: int| j == i && 0 <= j < str.len() && (str[j] == key));
                }
                return true;
            }
            i += 1;
        }
        proof {
            assert(!exists|j: int| 0 <= j < str.len() && (str[j] == key));
        }
        false
    }

    #[verifier::loop_isolation(false)]
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
                output_str.len() <= index,
                arr1.len() >= 0,
                arr1.len() <= usize::MAX,
                arr2.len() >= 0,
                arr2.len() <= usize::MAX,
                arr1.len() == arr1.len(), // This doesn't affect the invariant but is here for completeness
        {
            if !contains(arr2, arr1[index]) {
                output_str.push(arr1[index]);
                proof {
                    // Prove the invariant holds after the push
                    assert(forall|j: int| 0 <= j < output_str.len() ==> (arr1@.contains(# [trigger] output_str[j])
                        && !arr2@.contains(# [trigger] output_str[j])));
                }
            }
            index += 1;
            proof {
                // Prove the invariants
                assert(forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(
                    # [trigger] arr1[j])));
                assert(output_str.len() <= index);
            }
        }
        result = output_str;
        proof {
            // Final proofs
            assert(forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(
                    # [trigger] result[i])));
            assert(forall|i: int|
                0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || result@.contains(
                    # [trigger] arr1[i])));
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpes1v_zdd`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False