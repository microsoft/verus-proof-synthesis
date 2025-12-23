
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    reveal(Seq::filter); // Add this line to reveal the filter method

    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    assert(unique_arr@ == arr@.subrange(0, index as int).filter(
        |x: i32| count_frequency_rcr(arr@, x) == 1,
    ));
    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
            arr.len() == arr.len(), // Added invariant
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(arr@, 0, (index as int));
            assert(unique_arr@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ));
        }
    }
    proof {
        lemma_seq_subrange_all(arr@);
    }
    unique_arr
}


//             assert(unique_arr@ == arr@.subrange(0, index as int).filter(
//                 |x: i32| count_frequency_rcr(arr@, x) == 1,
//             ));
//   assertion failed: unique_arr@ == arr@.subrange(0, index as int).filter(                 |x: i32| count_frequency_rcr(arr@, x) == 1,             )

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False