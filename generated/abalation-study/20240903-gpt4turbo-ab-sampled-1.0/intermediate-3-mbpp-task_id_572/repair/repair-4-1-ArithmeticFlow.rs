
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            counter <= arr.len(), // Ensures counter does not exceed array length
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
    {
        if arr[index] == key {
            // Assert to protect against overflow. While logically redundant due to the loop invariant, it directly addresses overflow concerns.
            assert(counter < usize::MAX); // Introducing this assertion as a direct measure against overflow.
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