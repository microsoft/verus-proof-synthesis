
        if (arr[index] == key) {
            assert(counter < usize::MAX); // Ensure no overflow
            counter += 1;
        }


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False