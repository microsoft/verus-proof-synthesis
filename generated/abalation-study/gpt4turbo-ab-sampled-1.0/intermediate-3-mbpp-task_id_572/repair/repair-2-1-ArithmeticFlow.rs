
        if (arr[index] == key) {
            // Ensure that counter can be safely incremented without overflow
            // Assuming usize is used.
            assert(counter < usize::MAX); // This ensures we can safely add 1 to the counter.
            counter += 1;
        }


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False