
assert!((sum as i128).checked_add(arr[index] as i128).is_some(), "Preventing overflow");
sum = sum + arr[index] as i128;


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False