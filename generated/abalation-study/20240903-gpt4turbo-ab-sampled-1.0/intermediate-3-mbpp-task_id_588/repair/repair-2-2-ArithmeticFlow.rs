
    assert!(max_val >= min_val); // Ensures no underflow
    assert!(max_val - min_val <= i32::MAX as i32); // Redundant given the type and precondition, but illustrates direct assertion before subtraction
    max_val - min_val


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False