
    // ...
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            arr.len() > 0,
            arr.len() == arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            max_val == max_rcur(arr@.subrange(0, (index) as int)),
            min_val <= max_val,
            min_val == min_rcur(arr@.subrange(0, (index) as int)),
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Ensure the difference between max_val and min_val will not underflow/overflow
    assert!(min_val >= i32::MIN / 2 && max_val <= i32::MAX / 2); // Assert to reinforce no underflow/overflow will occur
    max_val - min_val
    // ...


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False