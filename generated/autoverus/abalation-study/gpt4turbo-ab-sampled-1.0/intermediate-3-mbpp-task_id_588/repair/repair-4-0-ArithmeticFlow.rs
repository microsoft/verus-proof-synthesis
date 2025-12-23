
    ...
    // Before performing the subtraction, assert that the difference is within i32 bounds 
    assert(max_val as int - min_val as int <= i32::MAX as int && max_val as int - min_val as int >= i32::MIN as int);
    max_val - min_val


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False