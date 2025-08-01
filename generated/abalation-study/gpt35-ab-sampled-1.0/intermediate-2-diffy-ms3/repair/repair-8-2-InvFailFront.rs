
assert(sum.len() == 1);
while (i < N as usize)
    invariant
        // ... other invariants
        sum.len() == 1,  // Moved from the while loop invariant
    {
        // ... loop body
    }


//             sum.len() == 1,
//   None: sum.len() == 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False