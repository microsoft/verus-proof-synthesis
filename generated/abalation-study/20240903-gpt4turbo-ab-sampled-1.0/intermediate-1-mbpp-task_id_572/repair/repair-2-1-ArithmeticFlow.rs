
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
            arr.len() == arr.len(), // loop invariant that specifies the length of the array arr
    {
        if arr[index] == key {
            // Ensure counter can safely be incremented (specifically for overflow).
            // Since `counter` represents occurrences within `arr`, it cannot logically exceed `arr.len()`
            assert(counter < usize::MAX); // Assert to prevent overflow before incrementing
            
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