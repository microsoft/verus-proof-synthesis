
assert!(forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i])));


//             forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i])),
//   None: forall|i: int| 0 <= i < result.len() ==> (!arr1@.contains(#[trigger] result[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False