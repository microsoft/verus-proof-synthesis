
            // Assertion to ensure the addition will not cause overflow or underflow
            assert(i128::MIN <= sum + arr[index] as i128 && sum + arr[index] as i128 <= i128::MAX);
            sum = sum + arr[index] as i128;


//             sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False