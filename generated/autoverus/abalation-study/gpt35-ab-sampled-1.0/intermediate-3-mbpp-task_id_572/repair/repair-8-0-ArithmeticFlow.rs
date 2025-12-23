
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
            index <= arr.len(),
    {
        if (arr[index] == key) {
            assert(counter + 1 <= arr.len() as usize) by {
                // Add supporting lemmas if needed
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