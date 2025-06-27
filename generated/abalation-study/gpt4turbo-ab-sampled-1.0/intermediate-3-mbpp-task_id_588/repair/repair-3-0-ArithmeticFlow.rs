
  // Assertion for preventing underflow/overflow, based on the provided condition and ensuring max_val >= min_val
  assert!(max_val >= min_val);  // Assert that max_val is always greater or equal to min_val

  max_val - min_val

Insert this line in your `difference_max_min` function right before the return operation:

rust
    assert!(max_val >= min_val); // Prevent underflow/overflow
    max_val - min_val


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False