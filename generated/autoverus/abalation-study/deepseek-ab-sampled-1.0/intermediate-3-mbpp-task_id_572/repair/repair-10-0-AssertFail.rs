

        proof {
            // Verify state after processing the current element
            lemma_seq_subrange_all(arr@.subrange(0, index as int));
            lemma_seq_subrange_ascend(arr@, 0, index as int);
            assert(unique_arr@ == arr@.subrange(0, index as int).filter(|x| count_frequency_rcr(arr@, x) == 1));
        }

//             assert(unique_arr@ == arr@.subrange(0, index as int).filter(|x| count_frequency_rcr(arr@, x) == 1));
//   assertion failed: unique_arr@ == arr@.subrange(0, index as int).filter(|x| count_frequency_rcr(arr@, x) == 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False