
        if (arr[index] == key) {
            assert(counter < arr.len()); // Ensure 'counter' before increment does not exceed 'arr.len()'
            counter += 1;
        }


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False