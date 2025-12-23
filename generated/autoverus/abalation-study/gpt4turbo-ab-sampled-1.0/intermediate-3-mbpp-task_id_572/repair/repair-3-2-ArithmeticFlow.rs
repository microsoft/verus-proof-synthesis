
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            // The counter cannot exceed index due to the condition of incrementation (an element matches the key)
            counter <= index,
            // Provides assurance that the counter won't overflow by proving it will always be within the length of the array
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
    {
        if (arr[index] == key) {
            // Before incrementing counter, ensure it is within safe range to prevent overflow
            assert(counter < usize::MAX); // Ensure counter does not overflow
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