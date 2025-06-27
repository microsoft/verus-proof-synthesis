
// Before the subtraction, we acknowledge the conditions protect against underflow/overflow.
// This is an explicative step rather than a strictly necessary one, given the context.
assert!(max_val >= min_val); // Enforced by the loop invariant.


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False