
if (arr[index] == key) {
    // Ensure that before incrementing, counter is less than the maximum value for usize
    // and logically, also ensure it does not exceed the length of the array since it counts elements.
    assert(counter < usize::MAX && counter < arr.len()); // Basic overflow check.
    counter += 1;
}


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False