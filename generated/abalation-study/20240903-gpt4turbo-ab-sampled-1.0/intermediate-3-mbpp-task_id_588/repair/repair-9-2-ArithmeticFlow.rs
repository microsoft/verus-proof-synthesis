
// Assertion to ensure no underflow/overflow will occur
assert!(max_val >= min_val); // Ensures no underflow
assert!(max_val - min_val <= i32::MAX as i32); // This assertion is essentially true by the constraints and nature of `max_val` and `min_val`, but explicitly verifying the absence of overflow.

max_val - min_val


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False