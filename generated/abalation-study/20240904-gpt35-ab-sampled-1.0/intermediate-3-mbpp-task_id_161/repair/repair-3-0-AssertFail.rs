
            proof {
                lemma_vec_push(output_str@, arr1[index], output_str.len());
                assert(forall|i: int| 0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])));
            } // Added by AI
            proof {
                lemma_vec_push(output_str@, arr1[index], output_str.len());
                lemma_vec_remove(arr1@, index);
                assert(forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
            } // Added by AI


//             assert(forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
//   assertion failed: forall|i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False