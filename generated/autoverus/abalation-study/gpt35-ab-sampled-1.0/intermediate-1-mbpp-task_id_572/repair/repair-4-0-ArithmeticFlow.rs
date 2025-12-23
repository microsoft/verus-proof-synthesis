
// ... (other code remains the same)

proof fn lemma_non_negative_counter(counter: int)
    requires
        counter >= 0,
    ensures
        counter + 1 > 0,
{
    // Prove that if counter is non-negative, then counter + 1 is positive
    // This lemma is used to assert the bound of counter += 1
}

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
            }
            counter += 1;
        }
        index += 1;
    }
    counter
}

// ... (other code remains the same)


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False