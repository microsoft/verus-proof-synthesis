
    // Before returning max_val - min_val, assert that the difference is within bounds
    assert!(max_val >= min_val); // Ensure no underflow
    // Given that array values are within i32::MIN/2 and i32::MAX/2, the assertion above is sufficient to guarantee the absence of overflow in the subtraction below.
    max_val - min_val


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False