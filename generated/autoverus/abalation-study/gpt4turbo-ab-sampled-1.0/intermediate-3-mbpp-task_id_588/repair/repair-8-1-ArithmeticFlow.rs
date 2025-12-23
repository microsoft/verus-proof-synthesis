
// Before final subtraction, let's assert the safe difference due to bounds on values
assert!(max_val >= min_val); // Ensuring max_val is not less than min_val, avoiding underflow


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False