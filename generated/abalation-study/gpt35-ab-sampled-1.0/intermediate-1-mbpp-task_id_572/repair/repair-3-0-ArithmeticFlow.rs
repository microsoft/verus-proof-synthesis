
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|j: int| 0 <= j < index ==> count_frequency_rcr(arr@, arr[j]) == counter,
    {
        if (arr[index] == key) {
            assert(counter >= 0) by {
                lemma_non_negative_counter(counter as int);
                lemma_non_negative_counter(counter + 1 as int);
            }
            counter += 1;
        }
        index += 1;
    }
    counter
}


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False