
assert(forall |k: int| 0 <= k < arr.len() ==> arr[k] % 2 == 0);


//             forall |k: int| 0 <= k < arr.len() ==> arr[k] % 2 == 0,
//   None: forall |k: int| 0 <= k < arr.len() ==> arr[k] % 2 == 0

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False