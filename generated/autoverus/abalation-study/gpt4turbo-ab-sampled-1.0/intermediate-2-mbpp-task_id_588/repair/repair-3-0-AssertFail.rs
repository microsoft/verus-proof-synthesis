
proof {
    let max_prf = max_rcur(arr@);
    assert(max_val as int == max_prf); // Proof for max_val
    let min_prf = min_rcur(arr@);
    assert(min_val as int == min_prf); // Proof for min_val
    // These assertions must inherently rely on properly adjusted loop invariants and the correct application of specification functions.
}


//         assert(min_prf == min_val); // Ensure the minimum value found is equal to the minimum value from min_rcur
//   assertion failed: min_prf == min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False